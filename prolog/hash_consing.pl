:- module(hash_consing,
          [ intern/2,               % ?Term, ?Id
            externalized/2,         % +TermWithIds, -External
            internalized/3,         % +Constructors, +External, -TermWithIds
            rewritten/1             % +Constructors
          ]).

/** <module> hash_consing: hash-consed terms whose Ids record a configurable shape, and a term rewrite that makes a program use them

A GENERIC LIBRARY: it knows no constructor of any calculus and keeps no
configuration but the templates files declare.

HOW TO USE IT. A file is written as the program that does not intern, loads
this library and names the constructors to intern, each by a template:

    :- module(steps, [step/2, built/2]).
    :- use_module(library(hash_consing), []).
    :- hash_consing:rewritten([apply(*, _), lambda(_), variable(_)]).

    step(apply(lambda(Body), Argument), beta(Body, Argument)).

    built(Function, Applied) :-
        Applied = apply(Function, variable(0)).

Files that hand such terms to each other declare the same templates, most
simply by including one file that holds the directive. Code that did not go
through the rewrite crosses the boundary explicitly:

    ?- hash_consing:internalized([apply(*, _), lambda(_), variable(_)],
                                 apply(lambda(variable(0)), variable(1)), Id),
       steps:step(Id, Result),
       hash_consing:externalized(Result, External).
    Id = '__hash_consed_apply/2'('lambda/1', <handle>),
    External = beta(variable(0), variable(1)).

With the list `[]` the file loads unchanged, which is the program without
interning. The test `test/hash_consing_rewrite.sh` prints what the rewrite
makes of its fixtures, `test/hash_consing_fixtures/`, and is the place to
read exact rewritten clauses.

`intern(?Term, ?Id)` IS ONE RELATION WITH TWO DIRECTIONS (user, 2026-09-17:
a binary predicate that upserts forwards and looks up backwards). Term is a
ground term whose rewritten subterms are Ids already. Called with Id bound it
looks the term up (and with Term bound as well it is a check that inserts
nothing); called with Id unbound, or bound to an Id pattern whose Handle is
unbound, it inserts Term unless it is there and answers its Id; a value that
is no Id matches nothing and the call fails, as a pattern that does not match
fails without interning (user ruling, 2026-09-17: an uninterned instance at
an Id position fails to unify rather than raising). The store is canonical
(the same term, the same Id), idempotent and monotone (it only grows and
backtracking does not shrink it), so an answer once given is never
contradicted. An Id is abstract: only `==`, `intern/2` and the two boundary
predicates look at it.

AN ID IS `'__hash_consed_Name/Arity'(Handle)` OR
`'__hash_consed_Name/Arity'(Shape, Handle)`. Name/Arity is the root constructor
of the term and Handle the node handle of one trie, the store. The root is in
the functor name so that the rewrite turns a head pattern `apply(F, X)` into
an Id pattern that first argument indexing tells apart by constructor, and a
value of another constructor, or no Id at all, fails at head unification
without a lookup (probe, 2026-09-17: with one functor for every Id, 156 ms
against 0.9 ms for 1000 calls over 2000 clauses). The prefix follows
SWI-Prolog's convention for names a library synthesises
(`library(apply_macros)`'s `'__aux_maplist/N_...'`); a leading `$` is reserved
for the system.

THE SHAPE is there for clauses told apart by an INNER constructor,

    step(apply(lambda(Body), Argument)) :- ...
    step(apply(closure_a(Capture), Argument)) :- ...

whose heads would otherwise be one Id pattern, every candidate clause paying
a lookup before it fails. Shape is ONE ATOM that spells the constructors
found below the root, as far as the constructor's template says (user,
2026-09-20: the Id keeps one layer, the shape may have several; the layers
are joined into one atom, not kept as several shapes; how deep is
configurable). The heads above become
`step('__hash_consed_apply/2'('lambda/1', Handle))` and
`step('__hash_consed_apply/2'('closure_a/1', Handle))`, and the deep index
SWI-Prolog builds on the first argument of the first argument tells them
apart without a lookup (benchmark, 2026-09-20: 1000 calls over 2000
such clauses, 621 ms without the shape and 3 ms with it; upserts 46 percent
slower; the store no larger).

THE ID STILL HAS ONE LAYER. The shape is not in the functor name, because a
shallow pattern `apply(F, X)` has to match the Ids of every shape and the set
of inner constructors is open across files; and the Id holds no Id of a
subterm, because a truncation would give one term two spellings and split
`==` and the table keys. A shape is a function of the content and the
template, so the Handle determines it and the store stays canonical.

THE CONFIGURATION IS A TEMPLATE, one syntax for every constructor (user,
2026-09-20: one syntax, not three; the template names the constructor, so no
indicator beside it; a depth of zero is another feature and is not offered).
An element of the directive's list is the constructor applied to one of these
at each argument position (a constructor of arity zero is its atom):

    _                  nothing is recorded about the argument
    *                  the root constructor of the argument is recorded
    a nested template  the root constructor is recorded and, when it is the
                       template's constructor, the template goes on below
                       it; alternatives are joined by `;`

`lambda(_)` records the root only and its Ids are
`'__hash_consed_lambda/1'(Handle)`. `apply(*, _)`
gives `apply(lambda(B), X)` the shape `'lambda/1'`; with
`apply(apply(*, _), _)`, `apply(apply(lambda(B), Y), X)` has the shape
`'apply/2(lambda/1)'` and `apply(lambda(B), X)` still `'lambda/1'`. An
argument that is no Id is written `-`. The reading has a precedent in
SWI-Prolog's mode-directed tabling, `:- table path(_, _, min)`.

THE SHAPE IS A FUNCTION OF THE TERM AND OF ITS OWN TEMPLATE, and of nothing
else: at a `*` the root is read off the functor name of the argument's Id,
with no lookup; each nested template costs an upsert one `trie_term/2` on the
argument's Id. The spelling of a shape is remembered in a trie keyed by its
structure, so an atom is built once per structure; the atoms are finitely
many, bounded by the templates and the constructors.

AT COMPILE TIME a pattern that determines everything its template records
gets the atom written into the head; a pattern that determines only part of
it gets an unbound shape, which is correct (the constructors of the pattern
are still checked by the lookups of the body) and unindexed. A nested
template reads the argument's own arguments off the occurrence of that
argument in the same clause, or off the store when its Id was baked. A
partial pattern is NOT expanded into one clause per completion: a file loaded
later brings new shapes, which the expanded clauses would silently miss. So
the deeper a template, the fewer patterns determine it.

ONE CONFIGURATION PER CONSTRUCTOR, PER PROCESS: a second declaration of a
constructor with another template raises while the file loads, because two
shapes of one term would not be `==` (agent design decision, 2026-09-20, not
objected to by the user; between files the library checks nothing else, by
the user's ruling of 2026-09-17: which files list which constructors is the
user's to arrange, for instance with one included file).

THE STORE IS ONE TRIE, used through SWI-Prolog's trie API directly (user,
2026-09-17, after a benchmark of four candidate stores: "use the trie"). Its
key is the term itself, constructor included (a trie shares a functor node
among all its keys), and its value is the key's own handle, written back with
`trie_update/3` right after the insertion, because inserting an existing
key with a different value raises instead of failing. It lives outside
the table space and `trie_property(Trie, value_count(Count))` counts it.

`externalized/2` AND `internalized/3` ARE THE BOUNDARY: the first replaces
every Id by its term, recursively, for printing, for writing a file and for a
content address; the second interns, bottom up, the instances of the
constructors whose templates it is given, for a term that did not come through the rewrite
(a toplevel query, `read_term/2`, a module that did not opt in, a term built
by `=..`).

`:- hash_consing:rewritten(Templates).` OPTS A FILE IN (user ruling,
2026-09-17: opt-in per file, the constructors passed to the directive, no
setting). Every clause read after it in that file, included files counted,
has each occurrence of a listed constructor turned into an
Id pattern and a call of `intern/2`, the direction of each call decided at
run time, so the file is written as the program that does not intern and
needs no mode declaration. Several directives in one file add up. An empty
list rewrites nothing. The library checks no consistency between files:
files that pass one constructor to each other must both list it, which the
user arranges, for instance with one included file (user ruling,
2026-09-17).

THE REWRITE OF A CLAUSE:

    head       fast path when the Handle of every top-level head occurrence
               is bound: look them up top down, then run the body, which
               keeps the last call; otherwise look up the bound ones top
               down, insert the ground ones bottom up, run the body, insert
               the rest bottom up (an instantiation error when a term is
               still not ground)
    body goal  when the variables of its terms are bound: insert bottom up
               and call; otherwise insert the ground ones, call, and then
               settle every occurrence top down (a lookup when the call
               bound the Id, an insertion when it made the term ground, an
               instantiation error when neither)
    ground     an occurrence that is ground in the source is interned while
               the file loads and its Id is written into the clause

Control constructs (`,`, `;`, `->`, `*->`, `\+`, `call/1`, `forall/2`, the
goal of `findall/3` and of `catch/3`, a module-qualified goal) are rewritten
inside. A listed constructor in the template or the result of `findall/3`,
in the catcher of `catch/3`, or in a DCG rule raises while the file loads.
Directives are not rewritten.

TWO RULES FOR A FILE THAT OPTS IN. (1) An instance of a listed constructor is
settled, ground or its Id bound, by the end of the goal it is handed to; a
term handed over half built and filled in later raises an instantiation
error. (2) Reflection sees Ids: `=..`, `functor/3`, `arg/3`, `write/1`,
`variant_sha1/2`, `term_hash/2` and ordering whose result depends on the
order see `'__hash_consed_Name/Arity'(Handle)`. Code that reads structure calls
`externalized/2` first, and code that builds an instance with them calls
`internalized/3` after; an instance left uninterned fails to unify at every
rewritten position. Using an Id as an opaque key, whose result does not
depend on the order (an assoc key, a sort to remove duplicates), is fine.

THIS MODULE REFLECTS ON SOURCE CLAUSES with `=..` while a file loads, a
mechanical boundary; nothing here chooses behaviour at run time by
reflection, and no closure is handed to another module.

FIXME: `trie_term/2` on an integer that is no node of the store crashes the
process with a segmentation fault (measured 2026-09-14 on `trie_term(42,
_)`); a forged `'__hash_consed_apply/2'(42)` reaches it. Only a bug makes
such a value. Candidate fix: none in the trie API; the assertz backends of
the benchmark raise instead, at the costs recorded there.

FIXME: on 2026-09-14, within tabled
compiles near a full stack, `trie_lookup/3` failed silently on a key of the
store and left the resource error pending. Here such a failure turns an
upsert into an insertion of an existing key, which raises, or a lookup into a
failure, which reads as no answer rather than `resource_error`. A direct probe
at 1m, 4m and 32m stacks on 2026-09-17 raised `resource_error(stack)` every
time and did not reproduce it.

FIXME: the order of two Ids depends on the insertion
history. Nothing checks that no code in an opted-in file reads that order;
it is a rule of the file, stated above.

FIXME: an Id written into a clause while the file loads
is a handle of this process. A file must be loaded from source, never
`qcompile`d nor saved in a state, and the store lives in one thread's global
variable.

FIXME: a file that uses a constructor another file
interns, without listing it, passes its instances uninterned; the rewritten
positions of the other file then fail to unify, silently. The library cannot
see it.
*/

:- use_module(library(error), [must_be/2]).
:- use_module(library(lists), [reverse/2, append/3]).

:- initialization(stores_created).

%!  stores_created  the store and the spellings of the shapes, two tries in
%   global variables of the loading thread.

stores_created :-
    trie_new(Store),
    nb_setval(hash_consing_store, Store),
    trie_new(Spellings),
    nb_setval(hash_consing_spellings, Spellings).

%   ---- the relation ----

%!  intern(?Term, ?Id)  Id is the Id of the ground term Term.

intern(Term, Id) :-
    nonvar(Id),
    !,
    id_parts(Id, _, _, Handle),
    (   nonvar(Handle)
    ->  trie_term(Handle, Stored),
        Term = Stored
    ;   upserted(Term, Id)
    ).
intern(Term, Id) :-
    upserted(Term, Id).

%!  upserted(+Term, ?Id)  insert Term unless it is stored, and answer its Id.

upserted(Term, Id) :-
    (   ground(Term)
    ->  true
    ;   throw(error(instantiation_error, context(hash_consing:intern/2, Term-Id)))
    ),
    nb_getval(hash_consing_store, Trie),
    (   trie_lookup(Trie, Term, Handle)
    ->  true
    ;   trie_insert(Trie, Term, pending, Handle),
        trie_update(Trie, Term, Handle)
    ),
    functor(Term, Name, Arity),
    configuration_of(Name, Arity, Configuration),
    id_of(Configuration, Term, Name, Arity, Handle, Id).

id_of(root_only, _, Name, Arity, Handle, Id) :-
    id_name(Name, Arity, IdName),
    compound_name_arguments(Id, IdName, [Handle]).
id_of(shaped(Records), Term, Name, Arity, Handle, Id) :-
    id_name(Name, Arity, IdName),
    (   term_shape(Term, Records, [], Shape)
    ->  true
    ;   throw(error(instantiation_error, context(hash_consing:intern/2, Term)))
    ),
    compound_name_arguments(Id, IdName, [Shape, Handle]).

%!  id_parts(+Value, -IdName, -Shape, -Handle)  Value is an Id or an Id
%   pattern; Shape is `none` for a constructor without a shape. Fails on any
%   other value.

id_parts(Value, IdName, Shape, Handle) :-
    compound(Value),
    compound_name_arity(Value, IdName, Arity),
    sub_atom(IdName, 0, _, _, '__hash_consed_'),
    id_arguments(Arity, Value, Shape, Handle).

id_arguments(1, Value, none, Handle) :-
    arg(1, Value, Handle).
id_arguments(2, Value, Shape, Handle) :-
    arg(1, Value, Shape),
    arg(2, Value, Handle).

%!  id_pattern(+Name, +Arity, -Id, -Handle)  an Id pattern of the constructor
%   as it is configured, its Handle and, if it has one, its shape unbound.

id_pattern(Name, Arity, Id, Handle) :-
    id_name(Name, Arity, IdName),
    configuration_of(Name, Arity, Configuration),
    (   Configuration == root_only
    ->  compound_name_arguments(Id, IdName, [Handle])
    ;   compound_name_arguments(Id, IdName, [_, Handle])
    ).

%!  id_name(+Name, +Arity, -IdName)  the functor name of the Ids of the
%   constructor Name/Arity, remembered once made, in both directions.

:- dynamic known_id_name/3.             % known_id_name(Name, Arity, IdName)
:- dynamic id_constructor/3.            % id_constructor(IdName, Name, Arity)

id_name(Name, Arity, IdName) :-
    (   known_id_name(Name, Arity, Known)
    ->  IdName = Known
    ;   format(atom(Made), '__hash_consed_~w/~d', [Name, Arity]),
        assertz(known_id_name(Name, Arity, Made)),
        assertz(id_constructor(Made, Name, Arity)),
        IdName = Made
    ).

%   ---- the configuration of a constructor ----

:- dynamic constructor_configuration/3. % constructor_configuration(Name, Arity, Configuration)

%!  configuration_of(+Name, +Arity, -Configuration)  `root_only`, or
%   `shaped(Records)` with one record per argument, `ignored` or
%   `root(Templates)`, Templates a list of `below(Name/Arity, Records)` for
%   the nested templates; a constructor met without a declaration is
%   registered as `root_only`.

configuration_of(Name, Arity, Configuration) :-
    (   constructor_configuration(Name, Arity, Known)
    ->  Configuration = Known
    ;   assertz(constructor_configuration(Name, Arity, root_only)),
        Configuration = root_only
    ).

%!  configuration_registered(+Name, +Arity, +Configuration)  the one
%   configuration of the constructor in this process; another raises.

configuration_registered(Name, Arity, Configuration) :-
    (   constructor_configuration(Name, Arity, Known)
    ->  (   Known == Configuration
        ->  true
        ;   throw(error(permission_error(reconfigure, interned_constructor, Name/Arity),
                        context(hash_consing:rewritten/1,
                                configured(Known)-declared(Configuration))))
        )
    ;   assertz(constructor_configuration(Name, Arity, Configuration))
    ).

%!  specification(+Template, -Name, -Arity, -Configuration)  an element of a
%   constructor list, a template, in the form the library keeps: ground, so
%   that two declarations of one constructor compare with `==`.

specification(Template, _, _, _) :-
    var(Template),
    !,
    throw(error(instantiation_error, context(hash_consing:rewritten/1, _))).
specification(Template, Name, Arity, Configuration) :-
    callable(Template),
    Template \== (*),
    Template \= (_ ; _),
    !,
    compound_name_arguments_or_atom(Template, Name, Arguments),
    length(Arguments, Arity),
    arguments_records(Arguments, Records),
    (   all_ignored(Records)
    ->  Configuration = root_only
    ;   Configuration = shaped(Records)
    ).
specification(Template, _, _, _) :-
    throw(error(type_error(constructor_template, Template), _)).

compound_name_arguments_or_atom(Term, Name, Arguments) :-
    (   atom(Term)
    ->  Name = Term,
        Arguments = []
    ;   compound_name_arguments(Term, Name, Arguments)
    ).

arguments_records([], []).
arguments_records([Argument | Arguments], [Record | Records]) :-
    argument_record(Argument, Record),
    arguments_records(Arguments, Records).

argument_record(Argument, ignored) :-
    var(Argument),
    !.
argument_record(*, root([])) :-
    !.
argument_record(Alternatives, root(Templates)) :-
    alternatives_list(Alternatives, List),
    templates_below(List, Templates).

alternatives_list(Alternatives, List) :-
    (   nonvar(Alternatives),
        Alternatives = (Left ; Right)
    ->  alternatives_list(Left, LeftList),
        alternatives_list(Right, RightList),
        append(LeftList, RightList, List)
    ;   List = [Alternatives]
    ).

%   A nested template whose own arguments are all ignored records nothing
%   below the root, which the root already says, and is left out.
templates_below([], []).
templates_below([Template | Templates], Belows) :-
    specification(Template, Name, Arity, Configuration),
    (   Configuration = shaped(Records)
    ->  Belows = [below(Name/Arity, Records) | Rest]
    ;   Belows = Rest
    ),
    templates_below(Templates, Rest),
    (   memberchk(below(Name/Arity, _), Rest)
    ->  throw(error(domain_error(one_template_per_constructor, Template), _))
    ;   true
    ).

all_ignored([]).
all_ignored([ignored | Records]) :-
    all_ignored(Records).

%   ---- shapes ----

%   A STRUCTURE is what a shape atom spells: a list, one description per
%   recorded argument, `other` for an argument that is no Id and
%   `constructor(Name/Arity, Structure)` otherwise, the inner structure being
%   `none` where no nested template goes on.

%!  term_shape(+Term, +Records, +Occurrences, -Atom)  the shape atom of Term
%   under its template. Fails when the term does not determine it: a
%   recorded argument is an unbound variable, or a nested template needs the
%   arguments of an Id pattern that is neither among Occurrences, the
%   `occurrence(Term, Id, Handle)` of the clause being rewritten, nor stored.
%   A ground Term always determines its shape.

term_shape(Term, Records, Occurrences, Atom) :-
    compound_name_arguments_or_atom(Term, _, Arguments),
    arguments_descriptions(Records, Arguments, Occurrences, Structure),
    nb_getval(hash_consing_spellings, Spellings),
    (   trie_lookup(Spellings, Structure, Known)
    ->  Atom = Known
    ;   structure_atom(Structure, Atom),
        trie_insert(Spellings, Structure, Atom)
    ).

arguments_descriptions([], [], _, []).
arguments_descriptions([ignored | Records], [_ | Arguments], Occurrences, Descriptions) :-
    !,
    arguments_descriptions(Records, Arguments, Occurrences, Descriptions).
arguments_descriptions([root(Templates) | Records], [Argument | Arguments], Occurrences,
                       [Description | Descriptions]) :-
    argument_description(Argument, Templates, Occurrences, Description),
    arguments_descriptions(Records, Arguments, Occurrences, Descriptions).

argument_description(Argument, _, _, _) :-
    var(Argument),
    !,
    fail.
argument_description(Argument, Templates, Occurrences, constructor(Name/Arity, Inner)) :-
    id_parts(Argument, IdName, _, _),
    !,
    id_constructor(IdName, Name, Arity),
    (   memberchk(below(Name/Arity, Records), Templates)
    ->  id_term(Argument, Occurrences, Below),
        compound_name_arguments_or_atom(Below, _, BelowArguments),
        arguments_descriptions(Records, BelowArguments, Occurrences, Inner)
    ;   Inner = none
    ).
argument_description(_, _, _, other).

%!  id_term(+Id, +Occurrences, -Term)  the term of an Id: stored, when its
%   Handle is bound; the occurrence's, when it is a pattern of the clause
%   being rewritten; fails otherwise.

id_term(Id, Occurrences, Term) :-
    id_parts(Id, _, _, Handle),
    (   nonvar(Handle)
    ->  trie_term(Handle, Term)
    ;   occurrence_term(Occurrences, Id, Term)
    ).

occurrence_term([occurrence(Candidate, CandidateId, _) | Occurrences], Id, Term) :-
    (   CandidateId == Id
    ->  Term = Candidate
    ;   occurrence_term(Occurrences, Id, Term)
    ).

%!  structure_atom(+Structure, -Atom)  the spelling: descriptions joined by
%   commas, `-` for `other`, `Name/Arity` and, in parentheses, what is below.

structure_atom(Structure, Atom) :-
    descriptions_texts(Structure, Texts),
    atomic_list_concat(Texts, ',', Atom).

descriptions_texts([], []).
descriptions_texts([Description | Descriptions], [Text | Texts]) :-
    description_text(Description, Text),
    descriptions_texts(Descriptions, Texts).

description_text(other, '-').
description_text(constructor(Name/Arity, none), Text) :-
    !,
    format(atom(Text), '~w/~d', [Name, Arity]).
description_text(constructor(Name/Arity, Inner), Text) :-
    structure_atom(Inner, InnerText),
    format(atom(Text), '~w/~d(~w)', [Name, Arity, InnerText]).

%   ---- the boundary ----

%!  externalized(+TermWithIds, -External)  every Id replaced by its term,
%   recursively.

externalized(Term, External) :-
    var(Term),
    !,
    External = Term.
externalized(Term, External) :-
    id_parts(Term, _, _, Handle),
    !,
    (   nonvar(Handle)
    ->  trie_term(Handle, Stored),
        externalized(Stored, External)
    ;   throw(error(instantiation_error, context(hash_consing:externalized/2, Term)))
    ).
externalized(Term, External) :-
    compound(Term),
    !,
    compound_name_arguments(Term, Name, Arguments),
    arguments_externalized(Arguments, ExternalArguments),
    compound_name_arguments(External, Name, ExternalArguments).
externalized(Term, Term).

arguments_externalized([], []).
arguments_externalized([Argument | Arguments], [External | Externals]) :-
    externalized(Argument, External),
    arguments_externalized(Arguments, Externals).

%!  internalized(+Constructors, +External, -TermWithIds)  every instance of a
%   constructor in Constructors interned, bottom up; an Id is kept as it is.
%   The list's elements are templates, as in the directive, and register the
%   same configurations.

internalized(Constructors, External, TermWithIds) :-
    must_be(list, Constructors),
    specifications_indicators(Constructors, Indicators),
    term_internalized(External, Indicators, TermWithIds).

specifications_indicators([], []).
specifications_indicators([Element | Elements], [Name/Arity | Indicators]) :-
    specification(Element, Name, Arity, Configuration),
    configuration_registered(Name, Arity, Configuration),
    specifications_indicators(Elements, Indicators).

term_internalized(Term, _, Internal) :-
    var(Term),
    !,
    Internal = Term.
term_internalized(Term, _, Internal) :-
    id_parts(Term, _, _, _),
    !,
    Internal = Term.
term_internalized(Term, Indicators, Internal) :-
    compound(Term),
    !,
    compound_name_arguments(Term, Name, Arguments),
    arguments_internalized(Arguments, Indicators, InternalArguments),
    compound_name_arguments(Rebuilt, Name, InternalArguments),
    compound_name_arity(Term, Name, Arity),
    instance_internalized(Name/Arity, Indicators, Rebuilt, Internal).
term_internalized(Term, Indicators, Internal) :-
    atom(Term),
    !,
    instance_internalized(Term/0, Indicators, Term, Internal).
term_internalized(Term, _, Term).

arguments_internalized([], _, []).
arguments_internalized([Argument | Arguments], Indicators, [Internal | Internals]) :-
    term_internalized(Argument, Indicators, Internal),
    arguments_internalized(Arguments, Indicators, Internals).

instance_internalized(Indicator, Indicators, Term, Internal) :-
    (   memberchk(Indicator, Indicators)
    ->  intern(Term, Internal)
    ;   Internal = Term
    ).

%   ---- the directive ----

%!  rewritten(+Templates)  the file being loaded opts in for the
%   constructors whose templates are in the list; several calls add up.

:- dynamic registered_constructor/3.     % registered_constructor(SourceFile, Name, Arity)

rewritten(Constructors) :-
    must_be(list, Constructors),
    (   prolog_load_context(source, File)
    ->  true
    ;   throw(error(context_error(nodirective, hash_consing:rewritten/1), _))
    ),
    constructors_registered(Constructors, File).

constructors_registered([], _).
constructors_registered([Element | Elements], File) :-
    specification(Element, Name, Arity, Configuration),
    configuration_registered(Name, Arity, Configuration),
    id_name(Name, Arity, _),
    (   registered_constructor(File, Name, Arity)
    ->  true
    ;   assertz(registered_constructor(File, Name, Arity))
    ),
    constructors_registered(Elements, File).

%   ---- the rewrite ----

%!  source_rewritten(+Source, -Rewritten)  the rewrite of one term read from a
%   file that opted in; fails, leaving the term to SWI-Prolog, otherwise.

source_rewritten(Source, _) :-
    var(Source),
    !,
    fail.
source_rewritten(end_of_file, _) :-
    !,
    prolog_load_context(source, File),
    prolog_load_context(file, File),
    retractall(registered_constructor(File, _, _)),
    fail.
source_rewritten((:- _), _) :-
    !,
    fail.
source_rewritten((?- _), _) :-
    !,
    fail.
source_rewritten(Source, Rewritten) :-
    prolog_load_context(source, File),
    registered_constructor(File, _, _),
    !,
    clause_rewritten(Source, File, Candidate),
    Candidate \=@= Source,
    Rewritten = Candidate.

clause_rewritten((Head --> Body), File, (Head --> Body)) :-
    !,
    listed_absent((Head --> Body), File, dcg_rule).
clause_rewritten((Head :- Body), File, Rewritten) :-
    !,
    rule_rewritten(Head, Body, File, Rewritten).
clause_rewritten(Head, File, Rewritten) :-
    rule_rewritten(Head, true, File, Rewritten).

%!  rule_rewritten(+Head, +Body, +File, -Rewritten)  the head's
%   occurrences scheduled around the rewritten body.

rule_rewritten(Qualifier:Head0, Body0, File, (Qualifier:Head :- Body)) :-
    !,
    plain_rule_rewritten(Head0, Body0, File, Head, Body).
rule_rewritten(Head0, Body0, File, (Head :- Body)) :-
    plain_rule_rewritten(Head0, Body0, File, Head, Body).

plain_rule_rewritten(Head0, Body0, File, Head, Body) :-
    arguments_of_abstracted(Head0, File, Head, Occurrences),
    body_rewritten(Body0, File, RewrittenBody),
    head_scheduled(Occurrences, RewrittenBody, Body).

%!  arguments_of_abstracted(+Callable0, +File, -Callable, -Occurrences)  the
%   arguments of a head or a goal abstracted (its own functor is a predicate
%   and is left alone), the ground occurrences interned now, and the others
%   listed bottom up as `occurrence(Term, Id, Handle)`.

arguments_of_abstracted(Callable0, File, Callable, Occurrences) :-
    compound(Callable0),
    !,
    compound_name_arguments(Callable0, Name, Arguments0),
    arguments_abstracted(Arguments0, File, Arguments, [], Reversed),
    compound_name_arguments(Callable, Name, Arguments),
    reverse(Reversed, BottomUp),
    occurrences_baked(BottomUp, Occurrences),
    shapes_determined(Occurrences).
arguments_of_abstracted(Callable, _, Callable, []).

arguments_abstracted([], _, [], Reversed, Reversed).
arguments_abstracted([Argument0 | Arguments0], File, [Argument | Arguments], Reversed0, Reversed) :-
    abstracted(Argument0, File, Argument, Reversed0, Reversed1),
    arguments_abstracted(Arguments0, File, Arguments, Reversed1, Reversed).

%!  abstracted(+Term0, +File, -Term, +Reversed0, -Reversed)  each occurrence
%   of a listed constructor replaced by an Id pattern, its subterms first,
%   the occurrences prepended as they are met.

abstracted(Term, _, Term, Reversed, Reversed) :-
    var(Term),
    !.
abstracted(Term0, File, Term, Reversed0, Reversed) :-
    compound(Term0),
    !,
    compound_name_arguments(Term0, Name, Arguments0),
    arguments_abstracted(Arguments0, File, Arguments, Reversed0, Reversed1),
    compound_name_arguments(Layer, Name, Arguments),
    compound_name_arity(Term0, Name, Arity),
    occurrence_abstracted(Name, Arity, Layer, File, Term, Reversed1, Reversed).
abstracted(Term0, File, Term, Reversed0, Reversed) :-
    atom(Term0),
    !,
    occurrence_abstracted(Term0, 0, Term0, File, Term, Reversed0, Reversed).
abstracted(Term, _, Term, Reversed, Reversed).

occurrence_abstracted(Name, Arity, Layer, File, Term, Reversed0, Reversed) :-
    (   registered_constructor(File, Name, Arity)
    ->  id_pattern(Name, Arity, Term, Handle),
        Reversed = [occurrence(Layer, Term, Handle) | Reversed0]
    ;   Term = Layer,
        Reversed = Reversed0
    ).

%!  occurrences_baked(+BottomUp, -Remaining)  an occurrence
%   whose term is ground is interned while the file loads, which binds its
%   Id in the clause; bottom up, so a parent of baked occurrences may become
%   ground in turn.

occurrences_baked([], []).
occurrences_baked([occurrence(Term, Id, Handle) | Occurrences], Remaining) :-
    (   ground(Term)
    ->  intern(Term, Id),
        occurrences_baked(Occurrences, Remaining)
    ;   Remaining = [occurrence(Term, Id, Handle) | Rest],
        occurrences_baked(Occurrences, Rest)
    ).

%!  shapes_determined(+BottomUp)  AT COMPILE TIME (above): an
%   occurrence of a shaped constructor whose pattern determines the whole
%   configured shape gets the shape atom written into its Id pattern, bottom
%   up so that a determined inner occurrence can determine an outer one; an
%   occurrence that determines only part of it keeps an unbound shape, which
%   matches every shape, and its constructors are still checked by the
%   lookups of the body.

shapes_determined(Occurrences) :-
    shapes_determined(Occurrences, Occurrences).

shapes_determined([], _).
shapes_determined([occurrence(Term, Id, _) | Rest], Occurrences) :-
    (   id_parts(Id, _, Shape, _),
        var(Shape),
        compound_name_arguments_or_atom(Term, Name, Arguments),
        length(Arguments, Arity),
        constructor_configuration(Name, Arity, shaped(Records)),
        term_shape(Term, Records, Occurrences, Atom)
    ->  Shape = Atom
    ;   true
    ),
    shapes_determined(Rest, Occurrences).

%!  head_scheduled(+BottomUp, +Body0, -Body)  the head row of THE REWRITE
%   OF A CLAUSE (above).

head_scheduled([], Body, Body) :-
    !.
head_scheduled(BottomUp, Body0, (Condition -> Fast ; General)) :-
    reverse(BottomUp, TopDown),
    top_level_occurrences(BottomUp, BottomUp, TopLevel),
    handles_bound(TopLevel, Condition),
    occurrences_goal(TopDown, intern, Lookups),
    occurrences_goal(TopDown, intern_if_bound, Settled),
    occurrences_goal(BottomUp, intern_if_unbound_and_ground, Inserted),
    occurrences_goal(BottomUp, intern_if_unbound, Finished),
    conjoined([Lookups, Body0], Fast),
    conjoined([Settled, Inserted, Body0, Finished], General).

%!  conjoined(+Goals, -Conjunction)  the goals in order, `true` left out.

conjoined(Goals, Conjunction) :-
    goals_kept(Goals, Kept),
    kept_conjoined(Kept, Conjunction).

goals_kept([], []).
goals_kept([Goal | Goals], Kept) :-
    (   Goal == true
    ->  Kept = Rest
    ;   Kept = [Goal | Rest]
    ),
    goals_kept(Goals, Rest).

kept_conjoined([], true).
kept_conjoined([Goal], Goal) :-
    !.
kept_conjoined([Goal | Goals], (Goal, Conjunction)) :-
    kept_conjoined(Goals, Conjunction).

top_level_occurrences([], _, []).
top_level_occurrences([Occurrence | Occurrences], All, TopLevel) :-
    Occurrence = occurrence(_, _, Handle),
    (   nested_in_another(Handle, All)
    ->  TopLevel = Rest
    ;   TopLevel = [Occurrence | Rest]
    ),
    top_level_occurrences(Occurrences, All, Rest).

nested_in_another(Handle, [occurrence(Term, _, _) | Occurrences]) :-
    (   term_variables(Term, Variables),
        variable_member(Handle, Variables)
    ->  true
    ;   nested_in_another(Handle, Occurrences)
    ).

variable_member(Variable, [Candidate | Candidates]) :-
    (   Variable == Candidate
    ->  true
    ;   variable_member(Variable, Candidates)
    ).

handles_bound([occurrence(_, _, Handle)], nonvar(Handle)) :-
    !.
handles_bound([occurrence(_, _, Handle) | Occurrences], (nonvar(Handle), Condition)) :-
    handles_bound(Occurrences, Condition).

%!  occurrences_goal(+Occurrences, +Step, -Goal)  the conjunction of one step
%   over the occurrences, in the order given.

occurrences_goal([], _, true).
occurrences_goal([Occurrence], Step, Goal) :-
    !,
    occurrence_goal(Step, Occurrence, Goal).
occurrences_goal([Occurrence | Occurrences], Step, (Goal, Goals)) :-
    occurrence_goal(Step, Occurrence, Goal),
    occurrences_goal(Occurrences, Step, Goals).

occurrence_goal(intern, occurrence(Term, Id, _),
                hash_consing:intern(Term, Id)).
occurrence_goal(intern_if_bound, occurrence(Term, Id, Handle),
                (nonvar(Handle) -> hash_consing:intern(Term, Id) ; true)).
occurrence_goal(intern_if_unbound, occurrence(Term, Id, Handle),
                (var(Handle) -> hash_consing:intern(Term, Id) ; true)).
occurrence_goal(intern_if_unbound_and_ground, occurrence(Term, Id, Handle),
                ((var(Handle), ground(Term)) -> hash_consing:intern(Term, Id) ; true)).
occurrence_goal(intern_if_ground, occurrence(Term, Id, _),
                (ground(Term) -> hash_consing:intern(Term, Id) ; true)).

%!  body_rewritten(+Body0, +File, -Body)  the control constructs rewritten
%   inside, every other goal by `goal_rewritten/3`.

body_rewritten(Goal, _, Goal) :-
    var(Goal),
    !.
body_rewritten((Left0, Right0), File, (Left, Right)) :-
    !,
    body_rewritten(Left0, File, Left),
    body_rewritten(Right0, File, Right).
body_rewritten((Left0 ; Right0), File, (Left ; Right)) :-
    !,
    body_rewritten(Left0, File, Left),
    body_rewritten(Right0, File, Right).
body_rewritten((Condition0 -> Then0), File, (Condition -> Then)) :-
    !,
    body_rewritten(Condition0, File, Condition),
    body_rewritten(Then0, File, Then).
body_rewritten((Condition0 *-> Then0), File, (Condition *-> Then)) :-
    !,
    body_rewritten(Condition0, File, Condition),
    body_rewritten(Then0, File, Then).
body_rewritten(\+ Goal0, File, \+ Goal) :-
    !,
    body_rewritten(Goal0, File, Goal).
body_rewritten(call(Goal0), File, call(Goal)) :-
    !,
    body_rewritten(Goal0, File, Goal).
body_rewritten(forall(Condition0, Action0), File, forall(Condition, Action)) :-
    !,
    body_rewritten(Condition0, File, Condition),
    body_rewritten(Action0, File, Action).
body_rewritten(findall(Template, Goal0, Result), File, findall(Template, Goal, Result)) :-
    !,
    listed_absent(Template-Result, File, findall_template_or_result),
    body_rewritten(Goal0, File, Goal).
body_rewritten(catch(Goal0, Catcher, Recovery0), File, catch(Goal, Catcher, Recovery)) :-
    !,
    listed_absent(Catcher, File, catch_catcher),
    body_rewritten(Goal0, File, Goal),
    body_rewritten(Recovery0, File, Recovery).
body_rewritten(Qualifier:Goal0, File, Qualifier:Goal) :-
    !,
    body_rewritten(Goal0, File, Goal).
body_rewritten(Goal0, File, Goal) :-
    goal_rewritten(Goal0, File, Goal).

%!  goal_rewritten(+Goal0, +File, -Goal)  the body goal row of THE REWRITE
%   OF A CLAUSE (above).

goal_rewritten(Goal0, File, Goal) :-
    arguments_of_abstracted(Goal0, File, Called, BottomUp),
    goal_scheduled(BottomUp, Called, Goal).

goal_scheduled([], Called, Called) :-
    !.
goal_scheduled(BottomUp, Called, (ground(Variables) -> Fast ; General)) :-
    reverse(BottomUp, TopDown),
    terms_variables(BottomUp, Variables),
    occurrences_goal(BottomUp, intern, Inserts),
    occurrences_goal(BottomUp, intern_if_ground, Settled),
    occurrences_goal(TopDown, intern, Finished),
    conjoined([Inserts, Called], Fast),
    conjoined([Settled, Called, Finished], General).

%!  terms_variables(+Occurrences, -Variables)  the variables of the
%   occurrences' terms other than their own Handles.

terms_variables(Occurrences, Variables) :-
    occurrences_terms(Occurrences, Terms),
    term_variables(Terms, All),
    occurrences_handles(Occurrences, Handles),
    variables_without(All, Handles, Variables).

occurrences_terms([], []).
occurrences_terms([occurrence(Term, _, _) | Occurrences], [Term | Terms]) :-
    occurrences_terms(Occurrences, Terms).

occurrences_handles([], []).
occurrences_handles([occurrence(_, _, Handle) | Occurrences], [Handle | Handles]) :-
    occurrences_handles(Occurrences, Handles).

variables_without([], _, []).
variables_without([Variable | Variables], Excluded, Kept) :-
    (   variable_member(Variable, Excluded)
    ->  Kept = Rest
    ;   Kept = [Variable | Rest]
    ),
    variables_without(Variables, Excluded, Rest).

%!  listed_absent(+Term, +File, +Place)  no listed constructor occurs in
%   Term, a place the rewrite does not schedule; raises otherwise.

listed_absent(Term, File, Place) :-
    abstracted(Term, File, _, [], Occurrences),
    (   Occurrences == []
    ->  true
    ;   throw(error(domain_error(term_without_rewritten_constructor, Term),
                    context(hash_consing:rewritten/1, Place)))
    ).

%   ---- the hook, last, so that this file's own clauses are read before it
%   is active ----

:- multifile user:term_expansion/2.
:- dynamic user:term_expansion/2.

user:term_expansion(Source, Rewritten) :-
    hash_consing:source_rewritten(Source, Rewritten).
