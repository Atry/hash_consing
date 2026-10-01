%   THE TEST OF THE HASH_CONSING LIBRARY, run from the root of the pack as
%       swipl -p library=prolog --stack-limit=32m --table-space=32m \
%             -g run_tests -t halt test/hash_consing.plt
%   Twelve plunit units, 86 tests. One unit per fixture file of
%   `hash_consing_fixtures/`, whose setup loads the fixture: its test
%   `snapshot` requires the errors the load raised, then the clauses the
%   load produced, rendered as text, to be byte for byte the file of
%   `hash_consing_snapshots/` named after the fixture, and each other test is
%   one query. The unit `library` checks that the library under test is this
%   checkout's, the unit `declarations` how lists of templates are declared,
%   the unit `interrupted_intern` that an interning interrupted by a limit
%   leaves no key that fails to answer its term, and the unit `concurrency`
%   that threads sharing the store declare, intern and spell shapes as one
%   thread would, and the unit `store` how the store grows and how its limit
%   and a thread's growth budget bound it. Failing it is a defect by
%   definition: what a rewrite produces and how `intern/2` answers are fixed
%   by the module comment of prolog/hash_consing.pl, not measured.
%
%   A CLAUSE IS RENDERED WITH ITS BAKED IDS EXTERNALIZED, `baked(Term)` in
%   place of the Id, because a handle is an address of this process and would
%   make the rendering differ from run to run. An Id pattern whose handle is a
%   variable is rendered as it is, its shape atom included.
%
%   AN ERROR WHILE LOADING IS RECORDED, not thrown: the fixtures that must be
%   refused raise inside term expansion, which SWI-Prolog reports as a
%   message and does not propagate, so a message hook records, under the
%   fixture being loaded, the formal term of each error and the warning that
%   a directive failed. The rendering cuts an absolute file name in them
%   down to its base name.
%
%   ALL FIXTURES SHARE THIS PROCESS, and a constructor has one list of
%   templates per process (module comment of prolog/hash_consing.pl):
%   `steps`, `inner_dispatch`, `reconfigured` and `calculus/1` declare
%   `apply/2` with `apply(*, _)`, so `spines` and `deep_calculus/1`, whose
%   template for applications is nested, name them `application/2`, and
%   `patterns` names its own `app/2`, `abs/1` and `ref/1`. The unit
%   `declarations` names constructors no other unit uses. The store and the
%   spellings of the shapes are shared too, so a count of either is only
%   compared before and after.
%
%   This file does not opt in; it reaches Ids through the library's
%   boundary predicates. The budget of each test is ONE SECOND, the
%   `timeout(1)` of its unit.

%   A WARNING OR AN ERROR PRINTED ANYWHERE FAILS THE RUN. plunit drops what
%   a unit's setup or a test prints when it succeeds, so a message that the
%   hook below does not record would otherwise pass unseen. Under these
%   flags plunit fails a test that prints a warning or an error, and `halt`
%   exits with status 1 once one was printed anywhere, a unit's setup
%   included; a message the hook records is not printed and does not count.
:- set_prolog_flag(on_warning, status).
:- set_prolog_flag(on_error, status).

:- use_module(library(plunit)).
:- use_module(library(hash_consing),
              [intern/2, represented/2, is_id/1, externalized/2, internalized/3, declared/1,
               store_property/1, store_growth_bounded/1]).
:- use_module(library(aggregate), [aggregate_all/3]).
:- use_module(library(lists), [member/2, append/3]).
:- use_module(library(readutil), [read_file_to_string/3]).
:- use_module(library(listing), [portray_clause/1]).
:- use_module(library(settings), [set_setting/2]).
:- use_module(library(time), [call_with_time_limit/2]).
:- use_module(library(thread), [concurrent_maplist/2, concurrent_maplist/3]).
:- use_module(library(apply), [maplist/3]).

%   A GOAL IS NEVER WRAPPED: `portray_clause/1` otherwise breaks a goal that
%   does not fit in the listing's line width, 78 columns, and a rendering
%   would then depend on the length of a constructor's name. Width 0 is the
%   setting's infinite width.
:- set_setting(listing:line_width, 0).

%!  test_directory(-Directory)
%
%   The directory of this file, against which the fixtures and the snapshots
%   are found.

:- dynamic test_directory/1.
:- prolog_load_context(directory, Directory),
   assertz(test_directory(Directory)).

%!  test_file(+Relative, -File)
%
%   Relative resolved against the directory of this file.

test_file(Relative, File) :-
    test_directory(Directory),
    directory_file_path(Directory, Relative, File).

%   ---- loading a fixture ----

:- dynamic load_error/2.                % load_error(Fixture, Formal)
:- dynamic loading/1.                   % loading(Fixture)

:- multifile user:message_hook/3.
user:message_hook(error(Formal, _), error, _) :-
    loading(Fixture),
    assertz(load_error(Fixture, Formal)).
user:message_hook(goal_failed(directive, _), warning, _) :-
    loading(Fixture),
    assertz(load_error(Fixture, directive_failed)).

%!  fixture_loaded(+Fixture)
%
%   The setup of a fixture's unit: the fixture file loaded, each error of the
%   load recorded as `load_error(Fixture, Formal)`. Nothing is imported: the
%   fixtures export predicates of the same name (`kind/2` in `inner_dispatch`
%   and `patterns`), which one module could not import from both, and the
%   tests call them qualified.

fixture_loaded(Fixture) :-
    fixture(Fixture, Relative, _, _),
    test_file(Relative, File),
    assertz(loading(Fixture)),
    catch(load_files(File, [if(true), imports([])]), Error,
          assertz(load_error(Fixture, thrown(Error)))),
    retractall(loading(Fixture)).

%   ---- rendering a fixture ----

%!  fixture_rendered(+Fixture, -Rendered)
%
%   The errors recorded while the fixture loaded, one `load_error(Formal)`
%   line each, then each predicate of the fixture's list with the clauses the
%   load produced, as one string.

fixture_rendered(Fixture, Rendered) :-
    fixture(Fixture, _, Module, Predicates),
    with_output_to(string(Rendered),
                   ( load_errors_printed(Fixture),
                     forall(member(Predicate, Predicates),
                            predicate_printed(Module, Predicate))
                   )).

load_errors_printed(Fixture) :-
    forall(load_error(Fixture, Formal0),
           \+ \+ ( paths_shortened(Formal0, Formal),
                   numbervars(Formal, 0, _),
                   format('load_error(~W)~n', [Formal, [quoted(true), numbervars(true)]])
                 )).

%!  paths_shortened(+Term, -Shortened)
%
%   Every absolute file name in Term as its base name, so that the rendering
%   does not depend on where the repository is checked out.

paths_shortened(Term, Term) :-
    var(Term),
    !.
paths_shortened(Term, Shortened) :-
    atom(Term),
    is_absolute_file_name(Term),
    !,
    file_base_name(Term, Shortened).
paths_shortened(Term, Shortened) :-
    compound(Term),
    !,
    compound_name_arguments(Term, Name, Arguments),
    arguments_paths_shortened(Arguments, ShortenedArguments),
    compound_name_arguments(Shortened, Name, ShortenedArguments).
paths_shortened(Term, Term).

arguments_paths_shortened([], []).
arguments_paths_shortened([Argument | Arguments], [Shortened | Shorteneds]) :-
    paths_shortened(Argument, Shortened),
    arguments_paths_shortened(Arguments, Shorteneds).

%!  predicate_printed(+Module, +Name/Arity)
%
%   The clauses as loaded.

predicate_printed(Module, Name/Arity) :-
    functor(Head, Name, Arity),
    format('predicate(~q)~n', [Name/Arity]),
    forall(clause(Module:Head, Body),
           ( baked_externalized((Head :- Body), Printed),
             portray_clause(Printed)
           )).

baked_externalized(Term, Printed) :-
    var(Term),
    !,
    Printed = Term.
baked_externalized(Term, Printed) :-
    compound(Term),
    compound_name_arity(Term, Name, Arity),
    sub_atom(Name, 0, _, _, '__hash_consed_'),
    arg(Arity, Term, Handle),
    nonvar(Handle),
    !,
    externalized(Term, External),
    Printed = baked(External).
baked_externalized(Term, Printed) :-
    compound(Term),
    !,
    compound_name_arguments(Term, Name, Arguments),
    arguments_baked_externalized(Arguments, PrintedArguments),
    compound_name_arguments(Printed, Name, PrintedArguments).
baked_externalized(Term, Term).

arguments_baked_externalized([], []).
arguments_baked_externalized([Argument | Arguments], [Printed | Printeds]) :-
    baked_externalized(Argument, Printed),
    arguments_baked_externalized(Arguments, Printeds).

%!  snapshot_read(+Fixture, -Snapshot)
%
%   The text of the fixture's file in `hash_consing_snapshots/`.

snapshot_read(Fixture, Snapshot) :-
    format(atom(Relative), 'hash_consing_snapshots/~w.txt', [Fixture]),
    test_file(Relative, File),
    read_file_to_string(File, Snapshot, []).

%   ---- the queries' helpers ----

%!  store_count(-Count)
%
%   How many terms the store holds.
store_count(Count) :-
    store_property(ids(Count)).

%!  spelling_count(-Count)
%
%   How many shape atoms the library has spelled.
spelling_count(Count) :-
    hash_consing:process_stores(_, Trie),
    trie_property(Trie, value_count(Count)).

%!  shape_indexed(+Head)
%
%   The just in time indexer built an index on the first argument of the first
%   argument, which is the shape.
shape_indexed(Head) :-
    predicate_property(Head, indexed(Indexes)),
    member(Index, Indexes),
    get_dict(arguments, Index, [1]),
    get_dict(position, Index, [1]),
    get_dict(realised, Index, true),
    !.

called_repeatedly(Goal) :-
    forall(between(1, 20, _), ( call(Goal) -> true ; true )).

%!  answers_its_term(+Term)
%
%   Term interns to an Id that externalizes back to Term.
answers_its_term(Term) :-
    intern(Term, Id),
    externalized(Id, Back),
    Back == Term.

%!  interned_forever(+Round, +Index)
%
%   Interns `time_probe(Round, Index, leaf)` and the probes after it until a
%   limit stops it, recording in the global variable
%   `interrupted_intern_count` the last Index interned.
interned_forever(Round, Index) :-
    intern(time_probe(Round, Index, leaf), _),
    nb_setval(interrupted_intern_count, Index),
    Next is Index + 1,
    interned_forever(Round, Next).

%!  numbered_template(+Prefix, +Number, -Template)
%
%   The template `Prefix_Number(_)`.
numbered_template(Prefix, Number, Template) :-
    format(atom(Name), '~w_~d', [Prefix, Number]),
    functor(Template, Name, 1).

%!  templates_declared_one_by_one(+Templates, +Worker)
%
%   Each template declared alone, in the order of the list.
templates_declared_one_by_one(Templates, _) :-
    forall(member(Template, Templates), declared([Template])).

%!  terms_interned(+Numbers, +Worker, -Ids)
%
%   The Id of `concurrently_interned(Number)` for each of Numbers, interned by
%   this thread, which installed nothing: the store is the process's.
terms_interned(Numbers, _, Ids) :-
    maplist(number_interned, Numbers, Ids).

%!  read_or_written(+Stored, +Worker, -Read)
%
%   An even worker interns the stored terms again, Read their Ids; an odd one
%   inserts new terms of the same constructor, Read `none`.
read_or_written(Stored, Worker, Read) :-
    (   Worker mod 2 =:= 0
    ->  maplist(read_beside_writers_interned, Stored, Read)
    ;   Low is 2001 + (Worker - 1) * 1250,
        High is Low + 1249,
        numlist(Low, High, New),
        maplist(read_beside_writers_interned, New, _),
        Read = none
    ).

read_beside_writers_interned(Number, Id) :-
    intern(read_beside_writers(Number), Id).

number_interned(Number, Id) :-
    intern(concurrently_interned(Number), Id).

%!  shapes_interned(+Numbers, +Worker, -Ids)
%
%   The Id of `concurrently_shaped(shape_Number, Worker)` for each of Numbers:
%   a term of this thread's own, whose shape every thread spells alike.
shapes_interned(Numbers, Worker, Ids) :-
    maplist(shape_interned(Worker), Numbers, Ids).

shape_interned(Worker, Number, Id) :-
    atom_concat(shape_, Number, Root),
    intern(concurrently_shaped(Root, Worker), Id).

%   ---- the fixtures ----

%!  fixture(?Fixture, ?File, ?Module, ?Predicates)
%
%   A fixture file, relative to this file's directory, the module it defines,
%   and the predicates its rendering shows.

fixture(steps, 'hash_consing_fixtures/steps.pl', steps,
        [step/2, callee/2, built/2, constant/1]).
fixture(spines, 'hash_consing_fixtures/spines.pl', spines,
        [head/2, inner/2]).
fixture(plain, 'hash_consing_fixtures/plain.pl', plain,
        [doubled/2, swapped/2]).
fixture(inner_dispatch, 'hash_consing_fixtures/inner_dispatch.pl', inner_dispatch, []).
fixture(reconfigured, 'hash_consing_fixtures/reconfigured.pl', reconfigured, []).
fixture(patterns, 'hash_consing_fixtures/patterns.pl', patterns,
        [kind/2, size/2, wrapped/2, first/2, built/2, unbound_built/1, brought_in/2]).
fixture(layers, 'hash_consing_fixtures/layers.pl', layers,
        [slot_made/2, slot_index/2, slot_read/2, linked_index/2, marked_name/2,
         is_slot/1]).

calculus([apply(*, _), lambda(_), variable(_), closure_a(_), closure_b]).
deep_calculus([application(application(*, _), _), lambda(_), variable(_), closure(_)]).
patterns_templates([app(abs(_), _), app(app(*, _), _), app(_, ref(_)), abs(_), ref(_)]).

%   ---- the units ----

:- begin_tests(library, [timeout(1)]).

%   The module under test is this checkout's, not a pack of the same name
%   installed elsewhere.
test(loaded_from_this_checkout, [true(File == Expected)]) :-
    module_property(hash_consing, file(File)),
    test_directory(Directory),
    file_directory_name(Directory, PackDirectory),
    directory_file_path(PackDirectory, 'prolog/hash_consing.pl', Expected).

:- end_tests(library).

:- begin_tests(steps, [setup(fixture_loaded(steps)), timeout(1)]).

test(snapshot, [true(Rendered == Snapshot)]) :-
    fixture_rendered(steps, Rendered),
    snapshot_read(steps, Snapshot).

test(shape_of_an_id, [nondet]) :-
    calculus(Templates),
    internalized(Templates, apply(lambda(variable(0)), variable(1)), Application),
    Application = '__hash_consed_apply/2'(Shape, _), Shape == 'lambda/1'.

test(shape_of_a_zero_arity_callee, [nondet]) :-
    calculus(Templates),
    internalized(Templates, apply(closure_b, variable(1)), Application),
    Application = '__hash_consed_apply/2'(Shape, _), Shape == 'closure_b/0'.

test(dispatch_lambda, [nondet]) :-
    calculus(Templates),
    internalized(Templates, apply(lambda(variable(0)), variable(1)), Application),
    steps:step(Application, Result), externalized(Result, External),
    External == beta(variable(0), variable(1)).

test(dispatch_closure, [nondet]) :-
    calculus(Templates),
    internalized(Templates, apply(closure_a(variable(7)), closure_b), Application),
    steps:step(Application, Result), externalized(Result, External),
    External == compiled(variable(7), closure_b).

test(dispatch_zero_arity, [nondet]) :-
    calculus(Templates),
    internalized(Templates, apply(closure_b, variable(3)), Application),
    steps:step(Application, Result), externalized(Result, External),
    External == constant(variable(3)).

test(dispatch_spine, [nondet]) :-
    calculus(Templates),
    internalized(Templates, apply(apply(closure_b, variable(1)), variable(2)), Application),
    steps:step(Application, Result), externalized(Result, External),
    External == spine(closure_b, variable(1), variable(2)).

test(one_answer_per_term, [nondet]) :-
    calculus(Templates),
    internalized(Templates, apply(lambda(variable(0)), variable(1)), Application),
    aggregate_all(count, steps:step(Application, _), Count), Count == 1.

test(partial_pattern_matches_every_shape, [nondet]) :-
    calculus(Templates),
    internalized(Templates, apply(closure_a(variable(7)), closure_b), Application),
    steps:callee(Application, Function), externalized(Function, External),
    External == closure_a(variable(7)).

test(body_goal_builds_the_shape, [nondet]) :-
    calculus(Templates), internalized(Templates, lambda(variable(0)), Function),
    steps:built(Function, Built),
    Built = '__hash_consed_apply/2'(Shape, _), Shape == 'lambda/1',
    internalized(Templates, apply(lambda(variable(0)), variable(0)), Application),
    Built == Application.

test(ground_occurrence_baked, [nondet]) :-
    steps:constant(Constant), externalized(Constant, External),
    External == apply(lambda(variable(0)), closure_b),
    calculus(Templates), internalized(Templates, External, Application),
    Constant == Application.

test(same_content_same_id, [nondet]) :-
    intern(variable(5), Variable), intern(lambda(Variable), Function),
    intern(apply(Function, Variable), First), intern(apply(Function, Variable), Second),
    First == Second.

test(backward, [nondet]) :-
    intern(variable(6), Variable), intern(lambda(Variable), Function),
    intern(apply(Function, Variable), Id),
    intern(Term, Id), Term == apply(Function, Variable).

test(wrong_shape_does_not_unify, [nondet]) :-
    calculus(Templates),
    internalized(Templates, apply(lambda(variable(0)), variable(1)), Application),
    \+ Application = '__hash_consed_apply/2'('closure_a/1', _).

test(spelling_remembered_once, [nondet]) :-
    intern(variable(8), FirstVariable), intern(closure_a(FirstVariable), FirstFunction),
    spelling_count(Before),
    intern(apply(FirstFunction, FirstVariable), _), spelling_count(Middle),
    intern(variable(9), SecondVariable), intern(closure_a(SecondVariable), SecondFunction),
    intern(apply(SecondFunction, SecondVariable), _),
    spelling_count(After),
    Middle >= Before, After =:= Middle.

test(argument_that_is_no_id, [nondet]) :-
    intern(apply(3, 4), Id), Id = '__hash_consed_apply/2'(Shape, _), Shape == '-'.

test(unground_term_raises, [error(instantiation_error)]) :-
    intern(apply(_, _), _).

test(externalized_internalized_inverse, [nondet]) :-
    calculus(Templates),
    External = f(apply(lambda(variable(0)), apply(closure_b, closure_b)), [variable(1)]),
    internalized(Templates, External, Internal), externalized(Internal, Back),
    Back == External.

:- end_tests(steps).

:- begin_tests(spines, [setup(fixture_loaded(spines)), timeout(1)]).

test(snapshot, [true(Rendered == Snapshot)]) :-
    fixture_rendered(spines, Rendered),
    snapshot_read(spines, Snapshot).

test(two_layers_in_the_shape, [nondet]) :-
    deep_calculus(Templates),
    internalized(Templates,
                 application(application(lambda(variable(0)), variable(1)), variable(2)),
                 Application),
    Application = '__hash_consed_application/2'(Shape, _),
    Shape == 'application/2(lambda/1)'.

test(template_ends_the_shape, [nondet]) :-
    deep_calculus(Templates),
    internalized(Templates,
                 application(application(application(lambda(variable(0)), variable(1)),
                                         variable(2)),
                             variable(3)),
                 Application),
    Application = '__hash_consed_application/2'(Shape, _),
    Shape == 'application/2(application/2)'.

test(dispatch_two_layers, [nondet]) :-
    deep_calculus(Templates),
    internalized(Templates,
                 application(application(closure(variable(0)), variable(1)), variable(2)),
                 Application),
    findall(Kind, spines:head(Application, Kind), Kinds),
    Kinds == [compiled_redex_under_an_application].

test(dispatch_one_layer, [nondet]) :-
    deep_calculus(Templates),
    internalized(Templates, application(lambda(variable(0)), variable(1)), Application),
    findall(Kind, spines:head(Application, Kind), Kinds), Kinds == [redex].

test(partial_pattern_still_right, [nondet]) :-
    deep_calculus(Templates),
    internalized(Templates,
                 application(application(closure(variable(0)), variable(1)), variable(2)),
                 Application),
    spines:inner(Application, Function), externalized(Function, External),
    External == closure(variable(0)).

test(partial_pattern_rejects_a_redex, [nondet]) :-
    deep_calculus(Templates),
    internalized(Templates, application(lambda(variable(0)), variable(1)), Application),
    \+ spines:inner(Application, _).

:- end_tests(spines).

:- begin_tests(plain, [setup(fixture_loaded(plain)), timeout(1)]).

test(snapshot, [true(Rendered == Snapshot)]) :-
    fixture_rendered(plain, Rendered),
    snapshot_read(plain, Snapshot).

test(upsert_then_externalize, [nondet]) :-
    plain:doubled(a, Doubled), externalized(Doubled, External), External == pair(a, a).

test(same_content_same_id, [nondet]) :-
    plain:doubled(a, Doubled), plain:swapped(Doubled, Swapped), Doubled == Swapped.

test(value_that_is_no_id_fails, [fail]) :-
    plain:doubled(_, foo).

test(uninterned_instance_fails, [fail]) :-
    plain:doubled(_, pair(a, a)).

test(both_sides_unknown_raises, [error(instantiation_error)]) :-
    plain:swapped(_, _).

:- end_tests(plain).

:- begin_tests(inner_dispatch, [setup(fixture_loaded(inner_dispatch)), timeout(1)]).

test(snapshot, [true(Rendered == Snapshot)]) :-
    fixture_rendered(inner_dispatch, Rendered),
    snapshot_read(inner_dispatch, Snapshot).

test(dispatch_by_inner_constructor, [nondet]) :-
    internalized([apply(*, _), closure_39(_)], apply(closure_39(x), y), Application),
    findall(Kind, inner_dispatch:kind(Application, Kind), Kinds), Kinds == [closure_39].

test(shape_indexed, [nondet]) :-
    internalized([apply(*, _), closure_39(_)], apply(closure_39(x), y), Application),
    called_repeatedly(inner_dispatch:kind(Application, _)),
    shape_indexed(inner_dispatch:kind(_, _)).

:- end_tests(inner_dispatch).

:- begin_tests(reconfigured, [setup(fixture_loaded(reconfigured)), timeout(1)]).

test(snapshot, [true(Rendered == Snapshot)]) :-
    fixture_rendered(reconfigured, Rendered),
    snapshot_read(reconfigured, Snapshot).

:- end_tests(reconfigured).

:- begin_tests(patterns, [setup(fixture_loaded(patterns)), timeout(1)]).

test(snapshot, [true(Rendered == Snapshot)]) :-
    fixture_rendered(patterns, Rendered),
    snapshot_read(patterns, Snapshot).

%   `app(abs(ref(0)), ref(1))` matches the first template and the third; the
%   first gives the shape.
test(first_template_gives_the_shape, [nondet]) :-
    patterns_templates(Templates),
    internalized(Templates, app(abs(ref(0)), ref(1)), Application),
    Application = '__hash_consed_app/2'(Shape, _), Shape == 'abs/1'.

test(second_template_records_two_layers, [nondet]) :-
    patterns_templates(Templates),
    internalized(Templates, app(app(abs(ref(0)), ref(1)), ref(2)), Application),
    Application = '__hash_consed_app/2'(Shape, _), Shape == 'app/2(abs/1)'.

test(third_template_records_the_second_argument, [nondet]) :-
    patterns_templates(Templates),
    internalized(Templates, app(ref(0), ref(1)), Application),
    Application = '__hash_consed_app/2'(Shape, _), Shape == 'ref/1'.

test(no_template_stays_plain, [nondet]) :-
    patterns_templates(Templates),
    internalized(Templates, ref(0), Function),
    internalized(Templates, abs(ref(1)), Argument),
    store_count(Before),
    internalized(Templates, app(ref(0), abs(ref(1))), Application),
    store_count(After),
    Application == app(Function, Argument),
    After =:= Before.

test(intern_fails_on_a_term_no_template_matches, [fail]) :-
    patterns_templates(Templates),
    internalized(Templates, ref(0), Function),
    internalized(Templates, abs(ref(1)), Argument),
    intern(app(Function, Argument), _).

test(intern_raises_without_templates,
     [error(existence_error(templates, undeclared_constructor/1))]) :-
    intern(undeclared_constructor(1), _).

test(is_id_tells_ids, [nondet]) :-
    patterns_templates(Templates),
    internalized(Templates, app(abs(ref(0)), ref(1)), Interned),
    internalized(Templates, app(ref(0), abs(ref(1))), Plain),
    is_id(Interned),
    \+ is_id(Plain),
    \+ is_id('__hash_consed_app/2'(_, _)).

test(kinds, [nondet, true(Kinds == [redex, redex_under_an_application, stuck, plain])]) :-
    patterns_templates(Templates),
    findall(Kind,
            ( member(External, [app(abs(ref(0)), ref(1)),
                                app(app(abs(ref(0)), ref(1)), ref(2)),
                                app(ref(0), ref(1)),
                                app(ref(0), abs(ref(1)))]),
              internalized(Templates, External, Application),
              patterns:kind(Application, Kind) ),
            Kinds).

test(undetermined_head_given_an_id, [nondet, true(Size == 4)]) :-
    patterns_templates(Templates),
    internalized(Templates, app(abs(ref(0)), ref(1)), Application),
    patterns:size(Application, Size).

test(undetermined_head_given_a_plain_term, [nondet, true(Size == 4)]) :-
    patterns_templates(Templates),
    internalized(Templates, app(ref(0), abs(ref(1))), Application),
    patterns:size(Application, Size).

test(undetermined_output_interned, [nondet]) :-
    patterns_templates(Templates),
    internalized(Templates, abs(ref(0)), Function),
    patterns:wrapped(Function, Wrapped),
    is_id(Wrapped),
    externalized(Wrapped, External), External == app(abs(ref(0)), abs(ref(0))).

test(undetermined_output_plain, [nondet]) :-
    patterns_templates(Templates),
    internalized(Templates, ref(0), Function),
    patterns:wrapped(Function, Wrapped),
    \+ is_id(Wrapped),
    externalized(Wrapped, External), External == app(ref(0), abs(ref(0))).

%   The program without interning answers `app(ref(1), abs(ref(0)))`; a clause
%   split into an Id version and a plain version would cut away the plain one.
test(cut_after_undetermined_occurrence, [nondet]) :-
    patterns_templates(Templates),
    internalized(Templates, ref(1), Function),
    internalized(Templates, abs(ref(0)), Argument),
    patterns:first([Function-Argument], First),
    externalized(First, External), External == app(ref(1), abs(ref(0))).

test(body_goal_decided_at_the_call, [nondet]) :-
    patterns_templates(Templates),
    internalized(Templates, abs(ref(1)), Lambda),
    internalized(Templates, ref(1), Reference),
    patterns:built(Lambda, Interned),
    patterns:built(Reference, Plain),
    is_id(Interned),
    Plain = app(Reference, _).

test(body_goal_undecided_raises, [error(instantiation_error)]) :-
    patterns:unbound_built(_).

test(represented_rejects_a_plain_term_that_must_be_interned, [fail]) :-
    patterns_templates(Templates),
    internalized(Templates, abs(ref(0)), Function),
    internalized(Templates, ref(1), Argument),
    represented(app(Function, Argument), app(Function, Argument)).

test(represented_decides_a_partial_layer, [nondet]) :-
    patterns_templates(Templates),
    internalized(Templates, abs(ref(0)), Function),
    represented(app(Function, _), Interned),
    Interned = '__hash_consed_app/2'(Shape, Handle), Shape == 'abs/1', var(Handle),
    internalized(Templates, ref(0), Reference),
    Layer = app(Reference, '__hash_consed_abs/1'(_)),
    represented(Layer, Plain),
    Plain == Layer.

test(represented_raises_when_undecided, [error(instantiation_error)]) :-
    represented(app(_, _), _).

%   The templates handed to internalized/3 in an opted-in file are kept as
%   written, so the call interns what the directive does.
test(templates_in_a_library_call_are_kept) :-
    patterns:brought_in(app(abs(ref(1)), ref(2)), Internal),
    is_id(Internal),
    patterns:kind(Internal, Kind),
    Kind == redex.

:- end_tests(patterns).

:- begin_tests(declarations, [timeout(1)]).

test(declared_twice_the_same) :-
    declared([declared_pair(abs(_), _), declared_pair(_, _)]),
    declared([declared_pair(abs(_), _), declared_pair(_, _)]).

test(declared_again_otherwise_raises,
     [error(permission_error(reconfigure, interned_constructor, declared_single/1))]) :-
    declared([declared_single(abs(_))]),
    declared([declared_single(ref(_))]).

test(unreachable_template_raises, [error(domain_error(reachable_template, _))]) :-
    declared([unreachable(_, _), unreachable(abs(_), _)]).

test(a_raising_declaration_registers_nothing,
     [error(existence_error(templates, unreachable_after_star/2))]) :-
    catch(declared([unreachable_after_star(*, _), unreachable_after_star(abs(_), _)]),
          error(domain_error(reachable_template, _), _),
          true),
    intern(unreachable_after_star(a, b), _).

%   `;` is a constructor like any other: the template requires a `;/2` term.
test(semicolon_is_a_constructor, [nondet]) :-
    Templates = [pick((abs(_) ; ref(_))), abs(_), ref(_)],
    internalized(Templates, pick(abs(ref(0))), Picked),
    \+ is_id(Picked),
    internalized(Templates, pick((abs(ref(0)) ; ref(1))), Chosen),
    is_id(Chosen).

:- end_tests(declarations).

%   AN INTERRUPTED INSERTION: `intern/2` interrupted between its insertion
%   and the write-back of the node's handle, by `call_with_inference_limit/3`
%   or by `call_with_time_limit/2`, leaves a store whose every key still
%   answers its own term (settled_handle/4 of prolog/hash_consing.pl). The
%   probes' constructors are declared in the unit's setup, every argument
%   `_`.

:- begin_tests(interrupted_intern,
               [setup(declared([inference_probe(_, _), time_probe(_, _, _)])), timeout(1)]).

%   Every inference limit from 1 to 300 on the interning of a fresh term:
%   one of them falls between the insertion and the write-back.
test(an_inference_limit_between_insertion_and_write_back) :-
    forall(between(1, 300, Limit),
           call_with_inference_limit(intern(inference_probe(Limit, leaf), _), Limit, _)),
    forall(between(1, 300, Limit),
           assertion(answers_its_term(inference_probe(Limit, leaf)))).

%   Time limits of a millisecond on a loop interning fresh terms: each
%   expires somewhere in an interning; the terms interned so far, and the
%   one being interned, still answer themselves.
test(a_time_limit_during_interning) :-
    forall(between(1, 50, Round),
           ( nb_setval(interrupted_intern_count, 0),
             catch(call_with_time_limit(0.001, interned_forever(Round, 1)),
                   time_limit_exceeded,
                   true),
             nb_getval(interrupted_intern_count, Count),
             Last is Count + 1,
             forall(between(1, Last, Index),
                    assertion(answers_its_term(time_probe(Round, Index, leaf)))) )).

:- end_tests(interrupted_intern).

%   THREADS SHARE ONE STORE: a thread that installs the store and the
%   spellings of the loading thread declares, interns and spells shapes
%   while other threads do the same. Eight workers do each thing at once;
%   what they leave is then read in one thread.

:- begin_tests(concurrency, [timeout(1)]).

%   Every constructor that the workers declared at once is registered once:
%   is_id/1 and intern/2 answer once on an Id of it.
test(a_constructor_declared_by_many_threads_is_registered_once) :-
    numlist(1, 2000, Numbers),
    maplist(numbered_template(concurrently_declared), Numbers, Templates),
    numlist(1, 8, Workers),
    concurrent_maplist(templates_declared_one_by_one(Templates), Workers),
    forall(member(Template, Templates),
           ( functor(Template, Name, 1),
             functor(Term, Name, 1),
             arg(1, Term, leaf),
             intern(Term, Id),
             aggregate_all(count, is_id(Id), 1),
             aggregate_all(count, intern(_, Id), 1) )).

%   A term that the workers intern at once has one Id, and no worker raises.
test(a_term_interned_by_many_threads_has_one_id) :-
    declared([concurrently_interned(_)]),
    numlist(1, 20000, Numbers),
    numlist(1, 8, Workers),
    concurrent_maplist(terms_interned(Numbers), Workers, IdLists),
    IdLists = [Ids | OtherIdLists],
    forall(member(OtherIds, OtherIdLists), OtherIds == Ids).

%   A shape that the workers spell at once, each for a term of its own, is
%   spelled without failing any of them.
test(a_shape_spelled_by_many_threads_fails_no_interning) :-
    declared([concurrently_shaped(*, _)]),
    numlist(1, 2000, Numbers),
    numlist(1, 8, Workers),
    concurrent_maplist(shapes_interned(Numbers), Workers, _).

%   Readers that intern stored terms while writers insert new ones of the
%   same constructor each get the one Id of every term, and none raises.
test(readers_beside_writers_read_one_id_per_term) :-
    declared([read_beside_writers(_)]),
    numlist(1, 2000, Stored),
    maplist(read_beside_writers_interned, Stored, StoredIds),
    numlist(1, 8, Workers),
    concurrent_maplist(read_or_written(Stored), Workers, ReadLists),
    forall(member(Read, ReadLists), ( Read == none ; Read == StoredIds )),
    numlist(2001, 12000, Written),
    maplist(read_beside_writers_interned, Written, WrittenIds),
    sort(WrittenIds, Distinct),
    length(Written, Count),
    length(Distinct, Count).

:- end_tests(concurrency).

%   ---- layers ----

:- begin_tests(layers, [setup(fixture_loaded(layers)), timeout(1)]).

test(snapshot, [true(Rendered == Snapshot)]) :-
    fixture_rendered(layers, Rendered),
    snapshot_read(layers, Snapshot).

test(represented_makes_an_id_of_a_written_layer) :-
    layers:slot_made(3, Slot),
    intern(slot(3), Expected),
    Slot == Expected.

test(represented_reads_a_written_layer_back) :-
    intern(slot(4), Slot),
    layers:slot_index(Slot, Index),
    Index == 4.

test(a_layer_handed_out_is_matched_as_written) :-
    intern(slot(5), Slot),
    layers:slot_read(Slot, Index),
    Index == 5.

test(a_listed_constructor_inside_a_layer_is_an_id) :-
    intern(slot(6), Slot),
    intern(link(Slot, Slot), Link),
    layers:linked_index(Link, Index),
    Index == 6.

test(a_head_layer_matches_a_plain_layer) :-
    layers:marked_name(marked(name), Name),
    Name == name.

test(a_head_layer_does_not_match_an_id, [fail]) :-
    intern(marked(name), Marked),
    layers:marked_name(Marked, _).

test(an_unread_occurrence_matches_an_id_of_its_constructor) :-
    intern(slot(7), Slot),
    layers:is_slot(Slot).

test(an_unread_occurrence_rejects_another_id, [fail]) :-
    intern(marked(name), Marked),
    layers:is_slot(Marked).

test(an_unread_occurrence_left_unbound_raises, [error(instantiation_error)]) :-
    layers:is_slot(_).

test(an_unknown_option_raises, [error(domain_error(rewritten_option, unknown))]) :-
    hash_consing:rewritten_with_options([], [unknown], hash_consing:rewritten/2).

test(a_skeleton_without_a_layer_raises, [error(domain_error(layer_skeleton, read(_)))]) :-
    hash_consing:rewritten_with_options([], [layer_arguments([read(_)])], hash_consing:rewritten/2).

:- end_tests(layers).

%   budget_spent_by_this_thread(+Main): sends Main `outcome(raised)` when
%   this thread, with a budget of one byte, may insert one new term but not
%   a second, and `outcome(within_budget)` when it may insert both.

budget_spent_by_this_thread(Main) :-
    store_growth_bounded(1),
    intern(grown_by_one_thread(1), _),
    catch(( intern(grown_by_one_thread(2), _), Outcome = within_budget ),
          error(resource_error(hash_consing_store), _),
          Outcome = raised),
    intern(grown_by_one_thread(1), _),
    thread_send_message(Main, outcome(Outcome)).

%   budget_inherited(+Main): with a budget of one byte, this thread spends
%   it on one new term and creates a thread that runs
%   budget_spent_by_this_thread/1 without setting a budget of its own; that
%   thread may insert one new term, its count being zero, but not a second,
%   and sends Main its outcome.

budget_inherited(Main) :-
    store_growth_bounded(1),
    intern(grown_by_an_inheriting_thread(0), _),
    thread_create(budget_spent_by_inheriting_thread(Main), Thread, []),
    thread_join(Thread, true).

budget_spent_by_inheriting_thread(Main) :-
    intern(grown_by_an_inheriting_thread(1), _),
    catch(( intern(grown_by_an_inheriting_thread(2), _), Outcome = within_budget ),
          error(resource_error(hash_consing_store), _),
          Outcome = raised),
    thread_send_message(Main, outcome(Outcome)).

%   grown_in_parallel_interned(+Group, +Number): `grown_in_parallel(Group,
%   Number)` interned.

grown_in_parallel_interned(Group, Number) :-
    intern(grown_in_parallel(Group, Number), _).

%   budgeted_halves(+Main, +Budget, +Numbers): with a budget of Budget bytes,
%   this thread interns the first half of Numbers, tells Main, waits for
%   `go_on`, interns the second half, and sends Main `outcome(raised)` if an
%   insertion raised, `outcome(within_budget)` otherwise.

budgeted_halves(Main, Budget, Numbers) :-
    store_growth_bounded(Budget),
    length(Numbers, Count),
    Half is Count // 2,
    length(FirstHalf, Half),
    append(FirstHalf, SecondHalf, Numbers),
    maplist(grown_in_parallel_interned(budgeted), FirstHalf),
    thread_send_message(Main, first_half_interned),
    thread_get_message(go_on),
    catch(( maplist(grown_in_parallel_interned(budgeted), SecondHalf),
            Outcome = within_budget ),
          error(resource_error(hash_consing_store), _),
          Outcome = raised),
    thread_send_message(Main, outcome(Outcome)).

:- begin_tests(store, [timeout(1)]).

%   A new term adds one Id to the store and its nodes to the trie; a term
%   interned again adds nothing.
test(a_new_term_adds_one_id) :-
    declared([counted_in_the_store(_)]),
    store_property(ids(Before)),
    intern(counted_in_the_store(1), Id),
    intern(counted_in_the_store(1), Again),
    store_property(ids(After)),
    store_property(nodes(Nodes)),
    store_property(bytes(Bytes)),
    Again == Id,
    After =:= Before + 1,
    Nodes >= After,
    Bytes > 0.

%   A thread that installed nothing reads the Id another thread made.
test(another_thread_reads_an_id_without_installing) :-
    declared([read_by_another_thread(_)]),
    intern(read_by_another_thread(1), Id),
    thread_create(( intern(Term, Id), Term == read_by_another_thread(1) ), Thread, []),
    thread_join(Thread, Status),
    Status == true.

%   The error for a constructor with no templates names declared/1.
test(the_missing_templates_message_names_declared,
     [true(sub_string(Text, _, _, _, "hash_consing:declared/1"))]) :-
    catch(intern(no_templates_anywhere(1), _), Error, true),
    message_text(Error, Text).

%   message_text(+Message, -Text): the text print_message/2 would print.
message_text(Message, Text) :-
    '$messages':translate_message(Message, Lines, []),
    with_output_to(string(Text), print_message_lines(current_output, '', Lines)).

%   A store past its limit raises a resource error on the next insertion and
%   still answers the terms it holds.
test(a_store_past_its_limit_raises) :-
    declared([bounded_in_the_store(_)]),
    intern(bounded_in_the_store(0), Held),
    store_property(bytes(Bytes)),
    Limit is Bytes - 1,
    setup_call_cleanup(
        set_prolog_flag(hash_consing_store_limit, Limit),
        ( catch(( intern(bounded_in_the_store(1), _), Raised = false ),
                error(resource_error(hash_consing_store), _),
                Raised = true),
          intern(bounded_in_the_store(0), Again) ),
        set_prolog_flag(hash_consing_store_limit, infinite)),
    Raised == true,
    Again == Held.

%   A thread whose budget is spent raises on its next insertion; a term
%   already in the store is still read, and other threads are not bounded.

test(a_thread_past_its_growth_budget_raises) :-
    declared([grown_by_one_thread(_)]),
    thread_self(Main),
    thread_create(budget_spent_by_this_thread(Main), Thread, []),
    thread_join(Thread, true),
    thread_get_message(outcome(Outcome)),
    Outcome == raised,
    intern(grown_by_one_thread(1000), _).

%   Two threads share the store; the first sets a budget, the second has
%   none. The second inserts 2000 terms between two halves of the first's
%   insertions, and the first's budget, room for its own terms only, is not
%   charged with them.

test(parallel_threads_do_not_charge_each_other) :-
    declared([grown_in_parallel(_, _)]),
    numlist(1, 50, Numbers),
    store_property(bytes(BytesBefore)),
    maplist(grown_in_parallel_interned(measured), Numbers),
    store_property(bytes(BytesAfter)),
    Budget is 2 * (BytesAfter - BytesBefore),
    thread_self(Main),
    thread_create(budgeted_halves(Main, Budget, Numbers), Budgeted, []),
    thread_get_message(first_half_interned),
    thread_create(forall(between(1, 2000, Number),
                         grown_in_parallel_interned(unbudgeted, Number)),
                  Unbudgeted, []),
    thread_join(Unbudgeted, true),
    thread_send_message(Budgeted, go_on),
    thread_join(Budgeted, true),
    thread_get_message(outcome(Outcome)),
    Outcome == within_budget.

%   A thread created by a thread with a budget inherits the budget with a
%   count of its own from zero, as it inherits `stack_limit`.

test(a_new_thread_inherits_the_budget_with_its_own_count) :-
    declared([grown_by_an_inheriting_thread(_)]),
    thread_self(Main),
    thread_create(budget_inherited(Main), Thread, []),
    thread_join(Thread, true),
    thread_get_message(outcome(Outcome)),
    Outcome == raised.

:- end_tests(store).
