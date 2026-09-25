#!/usr/bin/env swipl
%   THE TEST OF THE HASH_CONSING LIBRARY: ONE PROCESS PER FIXTURE, launched
%   by hash_consing_rewrite.sh as
%       swipl -q --stack-limit=32m --table-space=32m \
%             hash_consing_rewrite.pl -- --fixture=Name
%   It loads the fixture file of `hash_consing_fixtures/`, prints the
%   clauses the load produced and the outcome of the fixture's
%   queries, and hash_consing_rewrite.sh's output is compared with
%   hash_consing_rewrite_baseline.txt. Failing it is a defect by definition:
%   what a rewrite produces and how `intern/2` answers are fixed by the
%   module comment of prolog/hash_consing.pl, not measured.
%
%   A CLAUSE IS PRINTED WITH ITS BAKED IDS EXTERNALIZED, `baked(Term)` in
%   place of the Id, because a handle is an address of this process and would
%   make the baseline differ from run to run. An Id pattern whose handle is a
%   variable is printed as it is, its shape atom included.
%
%   AN ERROR WHILE LOADING IS PRINTED, not thrown: the fixtures that must be
%   refused raise inside term expansion, which SWI-Prolog reports as a
%   message and does not propagate, so a message hook records the formal
%   term of each error, an absolute file name in it cut down to its base
%   name, and the warning that a directive failed.
%
%   This file does not opt in; it reaches Ids through the library's
%   boundary predicates. The in-process budget is ONE SECOND.

:- use_module('../prolog/hash_consing', [intern/2, externalized/2, internalized/3]).
:- use_module(library(main), [argv_options/3]).
:- use_module(library(time), [call_with_time_limit/2]).
:- use_module(library(aggregate), [aggregate_all/3]).
:- initialization(main, main).

:- dynamic load_error/1.

:- multifile user:message_hook/3.
user:message_hook(error(Formal, _), error, _) :-
    loading_fixture,
    assertz(load_error(Formal)).
user:message_hook(goal_failed(directive, _), warning, _) :-
    loading_fixture,
    assertz(load_error(directive_failed)).

:- dynamic loading/0.

loading_fixture :-
    loading.

gate_time_limit(1).

main :-
    current_prolog_flag(argv, Arguments),
    argv_options(Arguments, _, Options),
    (   memberchk(fixture(Name), Options)
    ->  true
    ;   throw(error(existence_error(option, fixture), _))
    ),
    fixture(Name, File, Module, Predicates, Queries),
    format('fixture(~q)~n', [Name]),
    fixture_loaded(File),
    forall(member(Predicate, Predicates),
           predicate_printed(Module, Predicate)),
    forall(member(query(QueryName, Goal), Queries),
           query_printed(QueryName, Goal)).

fixture_loaded(File) :-
    assertz(loading),
    catch(load_files(File, [if(true)]), Error, assertz(load_error(thrown(Error)))),
    retractall(loading),
    forall(load_error(Formal0),
           \+ \+ ( paths_shortened(Formal0, Formal),
                   numbervars(Formal, 0, _),
                   format('load_error(~W)~n', [Formal, [quoted(true), numbervars(true)]])
                 )).

%!  paths_shortened(+Term, -Shortened)  every absolute file name in Term as
%   its base name, so that the output does not depend on where the
%   repository is checked out.

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

%!  predicate_printed(+Module, +Name/Arity)  the clauses as loaded.

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

%!  query_printed(+Name, +Goal)  `query(Name, true)`, `query(Name, false)`,
%   or `query(Name, error(Formal))`.

query_printed(Name, Goal) :-
    gate_time_limit(Limit),
    catch(( call_with_time_limit(Limit, Goal)
          ->  Outcome = true
          ;   Outcome = false
          ),
          Error,
          error_outcome(Error, Outcome)),
    format('query(~q, ~q)~n', [Name, Outcome]).

error_outcome(error(Formal, _), error(Formal)) :- !.
error_outcome(Error, thrown(Error)).

%   ---- the queries' helpers ----

store_count(Count) :-
    nb_getval(hash_consing_store, Trie),
    trie_property(Trie, value_count(Count)).

%!  spelling_count(-Count)  how many shape atoms the library has spelled.
spelling_count(Count) :-
    nb_getval(hash_consing_spellings, Trie),
    trie_property(Trie, value_count(Count)).

%!  check_inserts_nothing(+Term, +Id)  `intern(Term, Id)` with both bound
%   leaves the store's count as it was.
check_inserts_nothing(Term, Id) :-
    store_count(Before),
    (   intern(Term, Id)
    ->  Answered = true
    ;   Answered = false
    ),
    store_count(After),
    Before =:= After,
    Answered == false.

%!  shape_indexed(+Head)  the just in time indexer built an index on the
%   first argument of the first argument, which is the shape.
shape_indexed(Head) :-
    predicate_property(Head, indexed(Indexes)),
    member(Index, Indexes),
    get_dict(arguments, Index, [1]),
    get_dict(position, Index, [1]),
    get_dict(realised, Index, true),
    !.

called_repeatedly(Goal) :-
    forall(between(1, 20, _), ( call(Goal) -> true ; true )).

%   ---- the fixtures ----

calculus([apply(*, _), lambda(_), variable(_), closure_a(_), closure_b]).
deep_calculus([apply(apply(*, _), _), lambda(_), variable(_), closure_a(_)]).

fixture(steps, 'hash_consing_fixtures/steps.pl', steps,
        [step/2, callee/2, built/2, constant/1],
        [ query(shape_of_an_id,
                ( calculus(L), internalized(L, apply(lambda(variable(0)), variable(1)), T),
                  T = '__hash_consed_apply/2'(Shape, _), Shape == 'lambda/1' )),
          query(shape_of_a_zero_arity_callee,
                ( calculus(L), internalized(L, apply(closure_b, variable(1)), T),
                  T = '__hash_consed_apply/2'(Shape, _), Shape == 'closure_b/0' )),
          query(dispatch_lambda,
                ( calculus(L), internalized(L, apply(lambda(variable(0)), variable(1)), T),
                  steps:step(T, R), externalized(R, E), E == beta(variable(0), variable(1)) )),
          query(dispatch_closure,
                ( calculus(L), internalized(L, apply(closure_a(variable(7)), closure_b), T),
                  steps:step(T, R), externalized(R, E), E == compiled(variable(7), closure_b) )),
          query(dispatch_zero_arity,
                ( calculus(L), internalized(L, apply(closure_b, variable(3)), T),
                  steps:step(T, R), externalized(R, E), E == constant(variable(3)) )),
          query(dispatch_spine,
                ( calculus(L), internalized(L, apply(apply(closure_b, variable(1)), variable(2)), T),
                  steps:step(T, R), externalized(R, E),
                  E == spine(closure_b, variable(1), variable(2)) )),
          query(one_answer_per_term,
                ( calculus(L), internalized(L, apply(lambda(variable(0)), variable(1)), T),
                  aggregate_all(count, steps:step(T, _), Count), Count == 1 )),
          query(partial_pattern_matches_every_shape,
                ( calculus(L), internalized(L, apply(closure_a(variable(7)), closure_b), T),
                  steps:callee(T, F), externalized(F, E), E == closure_a(variable(7)) )),
          query(body_goal_builds_the_shape,
                ( calculus(L), internalized(L, lambda(variable(0)), F),
                  steps:built(F, B), B = '__hash_consed_apply/2'(Shape, _), Shape == 'lambda/1',
                  internalized(L, apply(lambda(variable(0)), variable(0)), T), B == T )),
          query(ground_occurrence_baked,
                ( steps:constant(C), externalized(C, E), E == apply(lambda(variable(0)), closure_b),
                  calculus(L), internalized(L, E, T), C == T )),
          query(same_content_same_id,
                ( intern(variable(5), V), intern(lambda(V), F),
                  intern(apply(F, V), First), intern(apply(F, V), Second), First == Second )),
          query(backward,
                ( intern(variable(6), V), intern(lambda(V), F), intern(apply(F, V), Id),
                  intern(Term, Id), Term == apply(F, V) )),
          query(wrong_shape_does_not_unify,
                ( calculus(L), internalized(L, apply(lambda(variable(0)), variable(1)), T),
                  \+ T = '__hash_consed_apply/2'('closure_a/1', _) )),
          query(spelling_remembered_once,
                ( intern(variable(8), V), intern(closure_a(V), F),
                  spelling_count(Before),
                  intern(apply(F, V), _), spelling_count(Middle),
                  intern(variable(9), W), intern(closure_a(W), G), intern(apply(G, W), _),
                  spelling_count(After),
                  Middle >= Before, After =:= Middle )),
          query(argument_that_is_no_id,
                ( intern(apply(3, 4), Id), Id = '__hash_consed_apply/2'(Shape, _), Shape == '-' )),
          query(unground_term_raises,
                intern(apply(_, _), _) ),
          query(externalized_internalized_inverse,
                ( calculus(L), External = f(apply(lambda(variable(0)), apply(closure_b, closure_b)), [variable(1)]),
                  internalized(L, External, Internal), externalized(Internal, Back), Back == External ))
        ]).
fixture(spines, 'hash_consing_fixtures/spines.pl', spines,
        [head/2, inner/2],
        [ query(two_layers_in_the_shape,
                ( deep_calculus(L),
                  internalized(L, apply(apply(lambda(variable(0)), variable(1)), variable(2)), T),
                  T = '__hash_consed_apply/2'(Shape, _), Shape == 'apply/2(lambda/1)' )),
          query(template_ends_the_shape,
                ( deep_calculus(L),
                  internalized(L, apply(apply(apply(lambda(variable(0)), variable(1)), variable(2)), variable(3)), T),
                  T = '__hash_consed_apply/2'(Shape, _), Shape == 'apply/2(apply/2)' )),
          query(dispatch_two_layers,
                ( deep_calculus(L),
                  internalized(L, apply(apply(closure_a(variable(0)), variable(1)), variable(2)), T),
                  findall(K, spines:head(T, K), Ks), Ks == [compiled_redex_under_an_application] )),
          query(dispatch_one_layer,
                ( deep_calculus(L), internalized(L, apply(lambda(variable(0)), variable(1)), T),
                  findall(K, spines:head(T, K), Ks), Ks == [redex] )),
          query(partial_pattern_still_right,
                ( deep_calculus(L),
                  internalized(L, apply(apply(closure_a(variable(0)), variable(1)), variable(2)), T),
                  spines:inner(T, F), externalized(F, E), E == closure_a(variable(0)) )),
          query(partial_pattern_rejects_a_redex,
                ( deep_calculus(L), internalized(L, apply(lambda(variable(0)), variable(1)), T),
                  \+ spines:inner(T, _) ))
        ]).
fixture(plain, 'hash_consing_fixtures/plain.pl', plain,
        [doubled/2, swapped/2],
        [ query(upsert_then_externalize,
                ( plain:doubled(a, D), externalized(D, E), E == pair(a, a) )),
          query(same_content_same_id,
                ( plain:doubled(a, D), plain:swapped(D, S), D == S )),
          query(value_that_is_no_id_fails,
                plain:doubled(_, foo) ),
          query(uninterned_instance_fails,
                plain:doubled(_, pair(a, a)) ),
          query(both_sides_unknown_raises,
                plain:swapped(_, _) )
        ]).
fixture(inner_dispatch, 'hash_consing_fixtures/inner_dispatch.pl', inner_dispatch, [],
        [ query(dispatch_by_inner_constructor,
                ( internalized([apply(*, _), closure_39(_)], apply(closure_39(x), y), T),
                  findall(K, inner_dispatch:kind(T, K), Ks), Ks == [closure_39] )),
          query(shape_indexed,
                ( internalized([apply(*, _), closure_39(_)], apply(closure_39(x), y), T),
                  called_repeatedly(inner_dispatch:kind(T, _)),
                  shape_indexed(inner_dispatch:kind(_, _)) ))
        ]).
fixture(reconfigured, 'hash_consing_fixtures/reconfigured.pl', reconfigured, [], []).
