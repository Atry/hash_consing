:- module(hash_consing,
          [ intern/2,               % ?Term, ?Id
            represented/2,          % ?Layer, ?Representation
            is_id/1,                % +Value
            externalized/2,         % +TermWithIds, -External
            internalized/3,         % +Templates, +External, -TermWithIds
            declared/1,             % +Templates
            rewritten/1             % +Templates
          ]).

/** <module> hash_consing: hash-consed terms selected by templates, whose Ids record a shape, and a term rewrite that makes a program use them

A GENERIC LIBRARY: it knows no constructor of any calculus and keeps no
configuration but the templates that files and `declared/1` declare.

HOW TO USE IT. A file is written as the program that does not intern, loads
this library and names, by templates, the terms to intern:

    :- module(steps, [step/2, built/2]).
    :- use_module(library(hash_consing), []).
    :- hash_consing:rewritten([apply(lambda(_), _), lambda(_), variable(_)]).

    step(apply(lambda(Body), Argument), beta(Body, Argument)).

    built(Function, Applied) :-
        Applied = apply(Function, variable(0)).

A term is interned when a template of its constructor matches it (TEMPLATES
ARE PATTERNS, below); here an application is interned when its first
argument is a lambda, and any other application stays a plain compound whose
arguments are represented in turn. Files that hand such terms to each other
declare the same templates, most simply by including one file that holds the
directive. Code that did not go through the rewrite crosses the boundary
explicitly:

    ?- hash_consing:internalized([apply(lambda(_), _), lambda(_), variable(_)],
                                 apply(lambda(variable(0)), variable(1)), Id),
       steps:step(Id, Result),
       hash_consing:externalized(Result, External).
    Id = '__hash_consed_apply/2'('lambda/1', <handle>),
    External = beta(variable(0), variable(1)).

With the list `[]` the file loads unchanged, which is the program without
interning. The test `test/hash_consing.plt` loads the fixtures in
`test/hash_consing_fixtures/` and compares what the rewrite makes of them
with the snapshots in `test/hash_consing_snapshots/`, the place to read
exact rewritten clauses.

`intern(?Term, ?Id)` IS ONE RELATION WITH TWO DIRECTIONS (user, 2026-09-17:
a binary predicate that upserts forwards and looks up backwards). Term is a
ground term whose subterms are represented already. Called with Id bound it
looks the term up (and with Term bound as well it is a check that inserts
nothing); called with Id unbound, or bound to an Id pattern whose Handle is
unbound, it inserts Term unless it is there and answers its Id. It fails,
inserting nothing, when no template of Term's constructor matches Term (user,
2026-09-26: a term that matches no template is not interned, even when its
constructor has templates), and raises `existence_error(templates,
Name/Arity)` when the constructor has no template in this process, which is
most likely a missing declaration (user, 2026-09-26, approving the change). A
value that is no Id matches nothing and the call fails, as a pattern that
does not match fails without interning (user ruling, 2026-09-17: an
uninterned instance at an Id position fails to unify rather than raising).
The store is canonical (the same term, the same Id), idempotent and monotone
(it only grows and backtracking does not shrink it), so an answer once given
is never contradicted. An Id is abstract: only `==`, `intern/2`,
`represented/2`, `is_id/1` and the two boundary predicates look at it.

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
    step(apply(closure(Capture), Argument)) :- ...

whose heads would otherwise be one Id pattern, every candidate clause paying
a lookup before it fails. Shape is ONE ATOM that spells the constructors
found below the root, as far as the term's template says (user, 2026-09-20:
the Id keeps one layer, the shape may have several; the layers are joined
into one atom, not kept as several shapes; how deep is configurable). Under
the templates `apply(lambda(_), _)` and `apply(closure(_), _)` the heads above
become `step('__hash_consed_apply/2'('lambda/1', Handle))` and
`step('__hash_consed_apply/2'('closure/1', Handle))`, and the deep index
SWI-Prolog builds on the first argument of the first argument tells them
apart without a lookup (benchmark, 2026-09-20: 1000 calls over 2000
such clauses, 621 ms without the shape and 3 ms with it; upserts 46 percent
slower; the store no larger).

THE ID STILL HAS ONE LAYER. The shape is not in the functor name, because a
shallow pattern `apply(F, X)` has to match the Ids of every shape and the set
of inner constructors is open across files; and the Id holds no Id of a
subterm, because a truncation would give one term two spellings and split
`==` and the table keys. A shape is a function of the content and of the
constructor's templates, so the Handle determines it and the store stays
canonical.

TEMPLATES ARE PATTERNS, in one syntax for every constructor (user,
2026-09-20: one syntax, not three; user, 2026-09-26: hash_consing is based on
patterns, not on constructors). An element of a list of templates is a
constructor applied to one of these at each argument position (a
constructor of arity zero is its atom):

    _                  any argument; nothing is recorded
    *                  any argument; its root constructor is recorded
    a nested template  an argument whose root constructor is the template's
                       and whose arguments match the template's arguments;
                       its root is recorded, and what the template records
                       below it

`*` records the root constructor of the term the argument stands for,
`Name/Arity`, whether that term is interned or not, and `-` for a number or a
string. There is no alternative inside a template, and `;` is an ordinary
constructor: the alternatives of a constructor are several templates in the
list, because Prolog's `;` is a disjunction whose two sides can both hold,
and templates are not predicates (user, 2026-09-26).

A CONSTRUCTOR'S TEMPLATES ARE TRIED IN ORDER, the order of the list, and the
first that matches a term is the term's template; the templates after it are
not looked at, and a term has one template or none (user, 2026-09-26: the
parts where templates overlap use the first matching template; matching
several templates at once has no meaning). The shape is what that template
records, spelled as the recorded descriptions joined by commas, `''` when it
records nothing. Under `apply(apply(*, _), _)` then `apply(*, _)`, the term
`apply(apply(lambda(B), Y), X)` has the shape `'apply/2(lambda/1)'` and
`apply(lambda(B), X)` the shape `'lambda/1'`; under `apply(apply(*, _), _)`
alone the second is not interned. A template that one earlier template
always takes first raises while it is declared, so a constructor whose
templates record nothing has the one template `Name(_, ..., _)`, and its Ids
have no shape; the Ids of any other constructor have one. Two templates that
record different positions can spell the same atom for different terms,
which only keeps the index from telling their clauses apart.

MATCHING AND RECORDING READ THE TERM, not how its subterms are represented:
an argument that is an Id is read through the store and an argument that is
a plain compound as it is, and both give the same root and arguments. At a
`*` the root of an Id is read off its functor name, with no lookup; a nested
template costs one `trie_term/2` on an argument that is an Id. The spelling
of a shape is remembered in a trie keyed by its structure, so an atom is
built once per structure; the atoms are finitely many, bounded by the
templates and the constructors.

ONE LIST OF TEMPLATES PER CONSTRUCTOR, PER PROCESS: the first declaration of
a constructor, by `rewritten/1`, `declared/1` or `internalized/3`, fixes its
list, and another declaration with other templates or another order raises
`permission_error(reconfigure, interned_constructor, Name/Arity)`, because
whether a term is interned and what its shape is must agree wherever it is
handed (agent design decision, 2026-09-20, for one template, and 2026-09-26
for a list, in plans the user approved; between files the library checks
nothing else, by the user's ruling of 2026-09-17: which files list which
constructors is the user's to arrange, for instance with one included file).
A constructor is never declared by being met.

THE STORE IS ONE TRIE, used through SWI-Prolog's trie API directly (user,
2026-09-17, after a benchmark of four candidate stores: "use the trie"). Its
key is the term itself, constructor included (a trie shares a functor node
among all its keys), and its value is the key's own handle, written back with
`trie_update/3` right after the insertion, because inserting an existing
key with a different value raises instead of failing. It lives outside
the table space and `trie_property(Trie, value_count(Count))` counts it.

A TERM THAT IS NOT INTERNED STAYS AS IT IS (user, 2026-09-26): a plain
compound of its constructor, whose arguments are represented in turn. The
REPRESENTATION of a term is its Id when a template of its constructor
matches it, and the term itself, with represented arguments, otherwise.

THE BOUNDARY: `externalized/2` replaces every Id by its term, recursively,
for printing, for writing a file and for a content address.
`internalized/3` declares the templates it is given and represents, bottom
up, the instances of their constructors, for a term that did not come
through the rewrite (a toplevel query, `read_term/2`, a module that did not
opt in, a term built by `=..`). `declared/1` only declares templates, for a
program whose constructors are made at run time. `is_id/1` tells an Id from
any other value. `represented(?Layer, ?Representation)` relates one layer, a
constructor applied to represented arguments, to its representation.

`:- hash_consing:rewritten(Templates).` OPTS A FILE IN (user ruling,
2026-09-17: opt-in per file, the constructors passed to the directive, no
setting). It declares the templates as `declared/1` does, and every clause
read after it in that file, included files counted, has each occurrence of a
constructor of the list rewritten as below, the direction of each call
decided at run time, so the file is written as the program that does not
intern and needs no mode declaration. Several directives in one file add up,
each declaring whole lists. An empty list rewrites nothing. The library
checks no consistency between files: files that pass one constructor to each
other must both list it, which the user arranges, for instance with one
included file (user ruling, 2026-09-17).

AN OCCURRENCE IS CLASSIFIED while the file loads, by comparing its source
pattern with each template of its constructor: every instance of the pattern
matches the template, none does, or some do.

    must intern       a template matches every instance: an Id pattern and
                      a call of `intern/2`; the shape is written in when the
                      first template that some instance matches matches them
                      all and each root it records is in the pattern
    must not intern   no template matches any instance: the layer itself,
                      written where the occurrence stood
    undetermined      otherwise: a fresh variable where the occurrence
                      stood, and a call of `represented/2`

A pattern whose variables are all filled with an atom no template names is
taken by a template only when that template has `_` or `*` there, and such a
template takes every instance, so no occurrence is missed as must intern.
The other two tests treat each occurrence of a variable apart, so a pattern
with a repeated variable can be classified undetermined, or left without its
shape, although its instances decide it; that is correct and unindexed. An
undetermined occurrence at the top of a head costs its clause the first
argument indexing of that argument: the clause is a candidate for every
call, so a call that a clause before it answers leaves a choice point on it
(measured 2026-09-26: with such a clause first in its predicate, calls on an
Id, a plain term and the other constructors' Ids were deterministic; with it
last, each of them left a choice point). Such a clause is not split into an
Id version and a plain version: called with that argument unbound, both
would run the body, and a cut in the first would prune the second.

THE REWRITE OF A CLAUSE:

    head       fast path when every top-level occurrence is given (the
               handle of an Id pattern bound; the variable of an undetermined
               occurrence bound, and not to an Id pattern whose handle is
               unbound): relate them to their layers top down, then run the
               body, which keeps the last call; otherwise relate the given
               ones top down, represent the ground ones bottom up, run the
               body, represent the rest bottom up (an instantiation error
               when a term that must be interned is still not ground, or an
               undetermined one is still undecided)
    body goal  when the variables of its layers are bound: represent bottom
               up and call; otherwise intern the ground ones and decide each
               undetermined one (its Id, an Id pattern whose handle is
               unbound, or the layer itself; an instantiation error when
               still undecided), call, and then settle every occurrence top
               down (a lookup when the call bound the Id, an insertion when
               it made the term ground, an instantiation error when
               neither)
    ground     an occurrence that is ground in the source is represented
               while the file loads, and its Id or its layer is written into
               the clause

Control constructs (`,`, `;`, `->`, `*->`, `\+`, `call/1`, `forall/2`, the
goal of `findall/3` and of `catch/3`, a module-qualified goal) are rewritten
inside. A listed constructor in the template or the result of `findall/3`,
in the catcher of `catch/3`, or in a DCG rule raises while the file loads.
Directives are not rewritten.

TWO RULES FOR A FILE THAT OPTS IN. (1) An instance of a listed constructor
whose interning is undetermined is decided when it is handed to a goal: what
is bound of it settles whether a template matches every completion or none
does, or the call raises an instantiation error; and every instance is
settled, ground or its Id bound, by the end of the goal it is handed to. The
first half is a DOWNGRADE of the rule before 0.2.0, which asked only for the
second: a term that matches no template stays as it is (user, 2026-09-26),
and a callee could not otherwise tell whether to receive an Id or a plain
term. (2) Reflection sees Ids: `=..`, `functor/3`, `arg/3`, `write/1`,
`variant_sha1/2`, `term_hash/2` and ordering whose result depends on the
order see `'__hash_consed_Name/Arity'(Handle)`. Code that reads structure calls
`externalized/2` first, and code that builds an instance with them calls
`internalized/3` after; an instance that must be interned and is left
uninterned fails to unify at every rewritten position. Using an Id as an
opaque key, whose result does not depend on the order (an assoc key, a sort
to remove duplicates), is fine.

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
:- use_module(library(lists), [reverse/2, member/2]).

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

%!  upserted(+Term, ?Id)  when a template of Term's constructor matches it,
%   insert Term unless it is stored, and answer its Id; fail, inserting
%   nothing, when none does.

upserted(Term, Id) :-
    (   ground(Term)
    ->  true
    ;   throw(error(instantiation_error, context(hash_consing:intern/2, Term-Id)))
    ),
    functor(Term, Name, Arity),
    templates_known(Name, Arity, hash_consing:intern/2, Templates, Kind),
    first_template_recorded(Templates, Term, Structure),
    nb_getval(hash_consing_store, Trie),
    (   trie_lookup(Trie, Term, Handle)
    ->  true
    ;   sig_atomic(inserted(Trie, Term, Handle))
    ),
    id_built(Name, Arity, Kind, Structure, Handle, Id).

%   inserted(+Trie, +Term, -Handle): the insertion and the write-back of the
%   key's own handle as its value, run under `sig_atomic/1` by upserted/2: a
%   signal between the two (a `call_with_time_limit/2` expiring) left the
%   value `pending` for good, and every later lookup of the key answered
%   `pending` as its handle, which `trie_term/2` rejects (seen 2026-09-26 in
%   lambda_jit's tests, whose readings run under a time limit).

inserted(Trie, Term, Handle) :-
    trie_insert(Trie, Term, pending, Handle),
    trie_update(Trie, Term, Handle).

%!  represented(?Layer, ?Representation)  Representation represents Layer, a
%   constructor applied to represented arguments: its Id when a template of
%   the constructor matches it, Layer itself otherwise.
%
%   Given an Id of the constructor, Layer is its stored term, or, when the
%   handle is unbound, Layer is interned into it and must be ground. Given
%   a plain term of the constructor, it is Layer, and no template may match
%   any completion of it: it is then not the representation of a term that
%   must be interned. Given nothing, Layer is represented as far as what is
%   bound of it decides: its Id when it is ground and a template matches it,
%   an Id pattern whose handle is unbound when every completion must be
%   interned, Layer itself when none may be, and an instantiation error when
%   what is bound does not decide. Any other value fails.

represented(Layer, Representation) :-
    (   var(Layer)
    ->  throw(error(instantiation_error,
                    context(hash_consing:represented/2, Layer-Representation)))
    ;   true
    ),
    functor(Layer, Name, Arity),
    templates_known(Name, Arity, hash_consing:represented/2, Templates, Kind),
    id_name(Name, Arity, IdName),
    (   var(Representation)
    ->  representation_made(Templates, Kind, Name, Arity, Layer, Representation)
    ;   id_parts(Representation, IdName, _, Handle)
    ->  (   nonvar(Handle)
        ->  trie_term(Handle, Stored),
            Layer = Stored
        ;   ground(Layer)
        ->  upserted(Layer, Representation)
        ;   throw(error(instantiation_error, context(hash_consing:represented/2, Layer)))
        )
    ;   functor(Representation, Name, Arity)
    ->  Layer = Representation,
        value_classified(Templates, Layer, Class, _),
        Class == must_not_intern
    ).

representation_made(Templates, Kind, Name, Arity, Layer, Representation) :-
    value_classified(Templates, Layer, Class, Structure),
    (   Class == must_intern
    ->  (   ground(Layer)
        ->  upserted(Layer, Representation)
        ;   id_built(Name, Arity, Kind, Structure, _, Representation)
        )
    ;   Class == must_not_intern
    ->  Representation = Layer
    ;   throw(error(instantiation_error, context(hash_consing:represented/2, Layer)))
    ).

%!  represented_settled(+Layer, ?Representation)  represented/2 at the end of
%   a rewritten head, where rule (1) of the module comment leaves no Id
%   pattern with an unbound handle: such a pattern raises an instantiation
%   error.

represented_settled(Layer, Representation) :-
    represented(Layer, Representation),
    (   id_parts(Representation, _, _, Handle),
        var(Handle)
    ->  throw(error(instantiation_error, context(hash_consing:represented/2, Layer)))
    ;   true
    ).

%!  is_id(+Value)  Value is an Id: an Id functor this process made, applied
%   to a bound handle.

is_id(Value) :-
    id_parts(Value, _, _, Handle),
    nonvar(Handle).

%!  id_parts(+Value, -IdName, -Shape, -Handle)  Value is an Id or an Id
%   pattern: its functor is one id_name/3 made, which the first argument
%   index of id_constructor/3 finds without scanning the name (the prefix
%   test it replaces took 30 percent of a lambda_jit read, 2026-09-26).
%   Shape is `none` for a constructor without a shape. Fails on any other
%   value.

id_parts(Value, IdName, Shape, Handle) :-
    compound(Value),
    compound_name_arity(Value, IdName, Arity),
    id_constructor(IdName, _, _),
    id_arguments(Arity, Value, Shape, Handle).

id_arguments(1, Value, none, Handle) :-
    arg(1, Value, Handle).
id_arguments(2, Value, Shape, Handle) :-
    arg(1, Value, Shape),
    arg(2, Value, Handle).

%!  id_built(+Name, +Arity, +Kind, +Structure, ?Handle, -Id)  the Id, or
%   the Id pattern, of the constructor with the handle Handle: no shape when
%   Kind is `root_only`, an unbound shape when Structure is `unknown`, and
%   otherwise the spelling of Structure.

id_built(Name, Arity, Kind, Structure, Handle, Id) :-
    id_name(Name, Arity, IdName),
    (   Kind == root_only
    ->  compound_name_arguments(Id, IdName, [Handle])
    ;   Structure == unknown
    ->  compound_name_arguments(Id, IdName, [_, Handle])
    ;   structure_spelled(Structure, Shape),
        compound_name_arguments(Id, IdName, [Shape, Handle])
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

%   ---- the templates of a constructor ----

%   A TEMPLATE IS KEPT PARSED, `template(Name/Arity, Arguments)` with one of
%   `ignored` (for `_`), `root` (for `*`) or a nested template per argument,
%   ground, so that two declarations of a constructor compare with `==`.

:- dynamic constructor_templates/4.     % constructor_templates(Name, Arity, Templates, Kind)

%!  declared(+Templates)  the constructors of the list declared for this
%   process, each with its templates in the order of the list.

declared(Templates) :-
    templates_declared(Templates, hash_consing:declared/1, _).

%!  templates_known(+Name, +Arity, +Context, -Templates, -Kind)  the declared
%   templates of the constructor, and `root_only` or `shaped`; raises when
%   the constructor has none.

templates_known(Name, Arity, Context, Templates, Kind) :-
    (   constructor_templates(Name, Arity, Templates, Kind)
    ->  true
    ;   throw(error(existence_error(templates, Name/Arity), context(Context, _)))
    ).

%!  templates_declared(+Templates, +Context, -Constructors)  the list parsed
%   and grouped by constructor, in the order of first appearance; every group
%   checked before any is registered; Constructors the `Name/Arity` of the
%   groups. Raises, registering nothing, on a malformed or unreachable
%   template and on a constructor already declared with another list.

templates_declared(Templates, Context, Constructors) :-
    must_be(list, Templates),
    templates_parsed(Templates, Context, Parsed),
    parsed_constructors(Parsed, [], Reversed),
    reverse(Reversed, Constructors),
    constructors_groups(Constructors, Parsed, Groups),
    groups_checked(Groups, Context),
    groups_registered(Groups).

parsed_constructors([], Constructors, Constructors).
parsed_constructors([_-template(Constructor, _) | Parsed], Seen, Constructors) :-
    (   memberchk(Constructor, Seen)
    ->  parsed_constructors(Parsed, Seen, Constructors)
    ;   parsed_constructors(Parsed, [Constructor | Seen], Constructors)
    ).

%   A GROUP is `group(Name/Arity, Written, Templates)`: the templates of one
%   constructor as written and as parsed, in the order of the list.

constructors_groups([], _, []).
constructors_groups([Constructor | Constructors], Parsed, [group(Constructor, Written, Templates) | Groups]) :-
    constructor_templates_parsed(Parsed, Constructor, Written, Templates),
    constructors_groups(Constructors, Parsed, Groups).

constructor_templates_parsed([], _, [], []).
constructor_templates_parsed([Template-Parsed | Pairs], Constructor, Written, Templates) :-
    (   Parsed = template(Constructor, _)
    ->  Written = [Template | WrittenRest],
        Templates = [Parsed | TemplatesRest]
    ;   Written = WrittenRest,
        Templates = TemplatesRest
    ),
    constructor_templates_parsed(Pairs, Constructor, WrittenRest, TemplatesRest).

groups_checked([], _).
groups_checked([group(Name/Arity, Written, Templates) | Groups], Context) :-
    templates_reachable(Written, Templates, [], Context),
    (   constructor_templates(Name, Arity, Known, _),
        Known \== Templates
    ->  templates_written(Known, KnownWritten),
        throw(error(permission_error(reconfigure, interned_constructor, Name/Arity),
                    context(Context, configured(KnownWritten)-declared(Written))))
    ;   true
    ),
    groups_checked(Groups, Context).

%!  templates_reachable(+Written, +Templates, +Earlier, +Context)  no
%   template is always taken first by one template before it.

templates_reachable([], [], _, _).
templates_reachable([Template | Written], [Parsed | Templates], Earlier, Context) :-
    (   member(EarlierTemplate, Earlier),
        template_covers(EarlierTemplate, Parsed)
    ->  throw(error(domain_error(reachable_template, Template), context(Context, _)))
    ;   templates_reachable(Written, Templates, [Parsed | Earlier], Context)
    ).

%!  template_covers(+Covering, +Covered)  every term Covered matches,
%   Covering matches too.

template_covers(template(Constructor, Coverings), template(Constructor, Covereds)) :-
    arguments_cover(Coverings, Covereds).

arguments_cover([], []).
arguments_cover([Covering | Coverings], [Covered | Covereds]) :-
    argument_covers(Covering, Covered),
    arguments_cover(Coverings, Covereds).

argument_covers(ignored, _).
argument_covers(root, _).
argument_covers(template(Constructor, Coverings), template(Constructor, Covereds)) :-
    arguments_cover(Coverings, Covereds).

groups_registered([]).
groups_registered([group(Name/Arity, _, Templates) | Groups]) :-
    (   constructor_templates(Name, Arity, _, _)
    ->  true
    ;   templates_kind(Templates, Kind),
        id_name(Name, Arity, _),
        assertz(constructor_templates(Name, Arity, Templates, Kind))
    ),
    groups_registered(Groups).

%   A constructor whose one template records nothing has Ids without a
%   shape; any other list has a template that records something.

templates_kind([template(_, Arguments)], root_only) :-
    all_ignored(Arguments),
    !.
templates_kind(_, shaped).

all_ignored([]).
all_ignored([ignored | Arguments]) :-
    all_ignored(Arguments).

compound_name_arguments_or_atom(Term, Name, Arguments) :-
    (   atom(Term)
    ->  Name = Term,
        Arguments = []
    ;   compound_name_arguments(Term, Name, Arguments)
    ).

%!  templates_parsed(+Templates, +Context, -Pairs)  each template paired with
%   its parsed form, `Template-Parsed`.

templates_parsed([], _, []).
templates_parsed([Template | Templates], Context, [Template-Parsed | Pairs]) :-
    template_parsed(Template, Context, Parsed),
    templates_parsed(Templates, Context, Pairs).

template_parsed(Template, Context, _) :-
    var(Template),
    !,
    throw(error(instantiation_error, context(Context, _))).
template_parsed(Template, Context, template(Name/Arity, Arguments)) :-
    callable(Template),
    Template \== (*),
    !,
    compound_name_arguments_or_atom(Template, Name, TemplateArguments),
    length(TemplateArguments, Arity),
    arguments_parsed(TemplateArguments, Context, Arguments).
template_parsed(Template, Context, _) :-
    throw(error(type_error(constructor_template, Template), context(Context, _))).

arguments_parsed([], _, []).
arguments_parsed([Argument | Arguments], Context, [Parsed | Parseds]) :-
    argument_parsed(Argument, Context, Parsed),
    arguments_parsed(Arguments, Context, Parseds).

argument_parsed(Argument, _, ignored) :-
    var(Argument),
    !.
argument_parsed(*, _, root) :-
    !.
argument_parsed(Argument, Context, Parsed) :-
    template_parsed(Argument, Context, Parsed).

%!  templates_written(+Templates, -Written)  parsed templates written back as
%   a user writes them, for an error to show.

templates_written([], []).
templates_written([Template | Templates], [Written | Writtens]) :-
    template_written(Template, Written),
    templates_written(Templates, Writtens).

template_written(template(Name/_, Arguments), Written) :-
    arguments_written(Arguments, WrittenArguments),
    (   WrittenArguments == []
    ->  Written = Name
    ;   compound_name_arguments(Written, Name, WrittenArguments)
    ).

arguments_written([], []).
arguments_written([Argument | Arguments], [Written | Writtens]) :-
    argument_written(Argument, Written),
    arguments_written(Arguments, Writtens).

argument_written(ignored, _).
argument_written(root, *).
argument_written(template(Constructor, Arguments), Written) :-
    template_written(template(Constructor, Arguments), Written).

%   ---- shapes ----

%   A STRUCTURE is what a shape atom spells: a list, one description per
%   recorded argument, `other` for an argument that stands for a number or a
%   string and `constructor(Name/Arity, Inner)` otherwise, Inner being `none`
%   where nothing is recorded below and the list of the descriptions below
%   otherwise. While a value leaves a recorded root open its description is
%   `unknown`, and a structure holding one is not spelled.
%
%   THE SAME COMPARISON serves the rewrite, on the source pattern of an
%   occurrence, and the store, on a term whose arguments are represented: a
%   value's root and arguments are read off a plain term or a pattern as they
%   are and off an Id through the store, and a variable, or the arguments of
%   an Id pattern whose handle is unbound, are open.

%!  value_classified(+Templates, +Value, -Class, -Structure)  Class is
%   `must_intern` when a template matches every term Value stands for,
%   `must_not_intern` when no template matches any, `undetermined`
%   otherwise. Structure is what the first template that matches some such
%   term records, when that template matches them all and every root it
%   records is known; `unknown` otherwise.

value_classified(Templates, Value, Class, Structure) :-
    templates_relations(Templates, Value, Relations),
    relations_class(Relations, Class),
    relations_structure(Relations, Structure).

templates_relations([], _, []).
templates_relations([Template | Templates], Value, [Relation-Descriptions | Relations]) :-
    template_relation(Template, Value, Relation, Descriptions),
    templates_relations(Templates, Value, Relations).

relations_class(Relations, must_intern) :-
    memberchk(instance-_, Relations),
    !.
relations_class(Relations, must_not_intern) :-
    \+ memberchk(overlap-_, Relations),
    !.
relations_class(_, undetermined).

relations_structure([], unknown).
relations_structure([Relation-Descriptions | Relations], Structure) :-
    (   Relation == disjoint
    ->  relations_structure(Relations, Structure)
    ;   Relation == instance,
        descriptions_known(Descriptions)
    ->  Structure = Descriptions
    ;   Structure = unknown
    ).

descriptions_known([]).
descriptions_known([Description | Descriptions]) :-
    description_known(Description),
    descriptions_known(Descriptions).

description_known(other).
description_known(constructor(_, Inner)) :-
    (   Inner == none
    ->  true
    ;   is_list(Inner),
        descriptions_known(Inner)
    ).

%!  first_template_recorded(+Templates, +Term, -Structure)  what the first
%   template that matches the ground Term records; fails when none does.

first_template_recorded([Template | Templates], Term, Structure) :-
    template_relation(Template, Term, Relation, Descriptions),
    (   Relation == instance
    ->  Structure = Descriptions
    ;   first_template_recorded(Templates, Term, Structure)
    ).

%!  template_relation(+Template, +Value, -Relation, -Descriptions)  whether
%   every term Value stands for matches the template (`instance`), none does
%   (`disjoint`) or some do (`overlap`), and what the template records on
%   them. Value's own root is the template's constructor.

template_relation(template(_, TemplateArguments), Value, Relation, Descriptions) :-
    compound_name_arguments_or_atom(Value, _, Arguments),
    arguments_relation(TemplateArguments, Arguments, instance, Relation, [], Reversed),
    reverse(Reversed, Descriptions).

arguments_relation([], [], Relation, Relation, Descriptions, Descriptions).
arguments_relation([TemplateArgument | TemplateArguments], [Argument | Arguments],
                   Relation0, Relation, Descriptions0, Descriptions) :-
    argument_relation(TemplateArgument, Argument, ArgumentRelation, Descriptions0, Descriptions1),
    relation_combined(Relation0, ArgumentRelation, Relation1),
    arguments_relation(TemplateArguments, Arguments, Relation1, Relation, Descriptions1, Descriptions).

argument_relation(ignored, _, instance, Descriptions, Descriptions).
argument_relation(root, Argument, instance, Descriptions, [Description | Descriptions]) :-
    value_root(Argument, Root),
    root_description(Root, Description).
argument_relation(template(Name/Arity, TemplateArguments), Argument, Relation,
                  Descriptions, [Description | Descriptions]) :-
    value_view(Argument, View),
    nested_relation(View, Name, Arity, TemplateArguments, Relation, Description).

nested_relation(open, Name, Arity, _, overlap, constructor(Name/Arity, unknown)).
nested_relation(other, Name, Arity, _, disjoint, constructor(Name/Arity, unknown)).
nested_relation(layer(ViewName/ViewArity, Arguments), Name, Arity, TemplateArguments,
                Relation, constructor(Name/Arity, Inner)) :-
    (   ViewName/ViewArity == Name/Arity
    ->  arguments_relation(TemplateArguments, Arguments, instance, Relation, [], Reversed),
        reverse(Reversed, Descriptions),
        (   Descriptions == []
        ->  Inner = none
        ;   Inner = Descriptions
        )
    ;   Relation = disjoint,
        Inner = unknown
    ).

relation_combined(disjoint, _, disjoint) :-
    !.
relation_combined(_, disjoint, disjoint) :-
    !.
relation_combined(instance, instance, instance) :-
    !.
relation_combined(_, _, overlap).

root_description(open, unknown).
root_description(other, other).
root_description(Name/Arity, constructor(Name/Arity, none)).

%!  value_root(+Value, -Root)  the root constructor of the term Value stands
%   for, `Name/Arity`, read off an Id's functor name without a lookup;
%   `open` for a variable, `other` for a number or a string.

value_root(Value, open) :-
    var(Value),
    !.
value_root(Value, Name/Arity) :-
    id_parts(Value, IdName, _, _),
    !,
    id_constructor(IdName, Name, Arity).
value_root(Value, Name/Arity) :-
    compound(Value),
    !,
    compound_name_arity(Value, Name, Arity).
value_root(Value, Value/0) :-
    atom(Value),
    !.
value_root(_, other).

%!  value_view(+Value, -View)  `layer(Name/Arity, Arguments)`, the root and
%   the arguments of the term Value stands for, an Id's read from the store
%   and open while its handle is unbound; `open` for a variable; `other` for
%   a number or a string.

value_view(Value, open) :-
    var(Value),
    !.
value_view(Value, layer(Name/Arity, Arguments)) :-
    id_parts(Value, IdName, _, Handle),
    !,
    id_constructor(IdName, Name, Arity),
    (   nonvar(Handle)
    ->  trie_term(Handle, Stored),
        compound_name_arguments_or_atom(Stored, _, Arguments)
    ;   length(Arguments, Arity)
    ).
value_view(Value, layer(Name/Arity, Arguments)) :-
    compound(Value),
    !,
    compound_name_arguments(Value, Name, Arguments),
    length(Arguments, Arity).
value_view(Value, layer(Value/0, [])) :-
    atom(Value),
    !.
value_view(_, other).

%!  structure_spelled(+Structure, -Atom)  the shape atom of a structure,
%   remembered in the trie of spellings so that it is built once.

structure_spelled(Structure, Atom) :-
    nb_getval(hash_consing_spellings, Spellings),
    (   trie_lookup(Spellings, Structure, Known)
    ->  Atom = Known
    ;   structure_atom(Structure, Atom),
        trie_insert(Spellings, Structure, Atom)
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

%!  internalized(+Templates, +External, -TermWithIds)  the templates declared
%   as declared/1 declares them, then every instance of their constructors
%   represented, bottom up: its Id when a template matches it, the plain
%   term otherwise; an Id is kept as it is.

internalized(Templates, External, TermWithIds) :-
    templates_declared(Templates, hash_consing:internalized/3, Constructors),
    term_internalized(External, Constructors, TermWithIds).

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

%   An instance whose templates were given is represented; one that is not
%   ground stays plain when no completion of it can match, and raises
%   otherwise, as intern/2 does on a term that is not ground.

instance_internalized(Name/Arity, Constructors, Layer, Internal) :-
    (   memberchk(Name/Arity, Constructors)
    ->  (   ground(Layer)
        ->  represented(Layer, Internal)
        ;   constructor_templates(Name, Arity, Templates, _),
            value_classified(Templates, Layer, Class, _),
            (   Class == must_not_intern
            ->  Internal = Layer
            ;   throw(error(instantiation_error, context(hash_consing:internalized/3, Layer)))
            )
        )
    ;   Internal = Layer
    ).

%   ---- the directive ----

%!  rewritten(+Templates)  the file being loaded opts in for the
%   constructors whose templates are in the list; several calls add up.

:- dynamic registered_constructor/3.     % registered_constructor(SourceFile, Name, Arity)

rewritten(Templates) :-
    must_be(list, Templates),
    (   prolog_load_context(source, File)
    ->  true
    ;   throw(error(context_error(nodirective, hash_consing:rewritten/1), _))
    ),
    templates_declared(Templates, hash_consing:rewritten/1, Constructors),
    constructors_registered(Constructors, File).

constructors_registered([], _).
constructors_registered([Name/Arity | Constructors], File) :-
    (   registered_constructor(File, Name, Arity)
    ->  true
    ;   assertz(registered_constructor(File, Name, Arity))
    ),
    constructors_registered(Constructors, File).

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
%   and is left alone), the ground occurrences represented now, and the
%   others listed bottom up as `occurrence(Class, Layer, Representation,
%   Handle)`: Class `id` for an occurrence that must be interned, its
%   Representation an Id pattern and Handle that pattern's handle, and
%   `undetermined(IdName)` for an undetermined one, its Representation and
%   its Handle the fresh variable written where it stood. An occurrence that
%   must not be interned is its layer, written in place, and is not listed.

arguments_of_abstracted(Callable0, File, Callable, Occurrences) :-
    compound(Callable0),
    !,
    compound_name_arguments(Callable0, Name, Arguments0),
    arguments_abstracted(Arguments0, File, Arguments, [], Reversed),
    compound_name_arguments(Callable, Name, Arguments),
    reverse(Reversed, BottomUp),
    occurrences_baked(BottomUp, Occurrences).
arguments_of_abstracted(Callable, _, Callable, []).

arguments_abstracted([], _, [], Reversed, Reversed).
arguments_abstracted([Argument0 | Arguments0], File, [Argument | Arguments], Reversed0, Reversed) :-
    abstracted(Argument0, File, Argument, Reversed0, Reversed1),
    arguments_abstracted(Arguments0, File, Arguments, Reversed1, Reversed).

%!  abstracted(+Term0, +File, -Term, +Reversed0, -Reversed)  each occurrence
%   of a listed constructor replaced by its representation in the clause,
%   its subterms first, the listed occurrences prepended as they are met.

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
    occurrence_abstracted(Name, Arity, Term0, Layer, File, Term, Reversed1, Reversed).
abstracted(Term0, File, Term, Reversed0, Reversed) :-
    atom(Term0),
    !,
    occurrence_abstracted(Term0, 0, Term0, Term0, File, Term, Reversed0, Reversed).
abstracted(Term, _, Term, Reversed, Reversed).

%!  occurrence_abstracted(+Name, +Arity, +Source, +Layer, +File,
%   -Representation, +Reversed0, -Reversed)  AN OCCURRENCE IS CLASSIFIED
%   (above) by its source pattern Source, and written as an Id pattern, as
%   its layer, or as a fresh variable.

occurrence_abstracted(Name, Arity, Source, Layer, File, Representation, Reversed0, Reversed) :-
    (   registered_constructor(File, Name, Arity)
    ->  constructor_templates(Name, Arity, Templates, Kind),
        value_classified(Templates, Source, Class, Structure),
        occurrence_represented(Class, Name, Arity, Kind, Structure, Layer, Representation,
                               Reversed0, Reversed)
    ;   Representation = Layer,
        Reversed = Reversed0
    ).

occurrence_represented(must_intern, Name, Arity, Kind, Structure, Layer, Id,
                       Reversed, [occurrence(id, Layer, Id, Handle) | Reversed]) :-
    id_built(Name, Arity, Kind, Structure, Handle, Id).
occurrence_represented(must_not_intern, _, _, _, _, Layer, Layer, Reversed, Reversed).
occurrence_represented(undetermined, Name, Arity, _, _, Layer, Variable,
                       Reversed, [occurrence(undetermined(IdName), Layer, Variable, Variable) | Reversed]) :-
    id_name(Name, Arity, IdName).

%!  occurrences_baked(+BottomUp, -Remaining)  an occurrence whose layer is
%   ground is represented while the file loads, which binds its Id in the
%   clause; bottom up, so a parent of baked occurrences may become ground in
%   turn.

occurrences_baked([], []).
occurrences_baked([Occurrence | Occurrences], Remaining) :-
    Occurrence = occurrence(Class, Layer, Representation, _),
    (   ground(Layer)
    ->  occurrence_represented_now(Class, Layer, Representation),
        occurrences_baked(Occurrences, Remaining)
    ;   Remaining = [Occurrence | Rest],
        occurrences_baked(Occurrences, Rest)
    ).

occurrence_represented_now(id, Layer, Id) :-
    intern(Layer, Id).
occurrence_represented_now(undetermined(_), Layer, Variable) :-
    represented(Layer, Variable).

%!  head_scheduled(+BottomUp, +Body0, -Body)  the head row of THE REWRITE
%   OF A CLAUSE (above).

head_scheduled([], Body, Body) :-
    !.
head_scheduled(BottomUp, Body0, (Condition -> Fast ; General)) :-
    reverse(BottomUp, TopDown),
    top_level_occurrences(BottomUp, BottomUp, TopLevel),
    occurrences_given(TopLevel, Condition),
    occurrences_goal(TopDown, related, Lookups),
    occurrences_goal(TopDown, related_if_given, Settled),
    occurrences_goal(BottomUp, represented_if_ground, Inserted),
    occurrences_goal(BottomUp, settled_unless_given, Finished),
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

%   An occurrence is at the top when its handle is in the layer of no other
%   listed occurrence; the layer of an occurrence that must not be interned
%   is written in place and does not hide what it holds.

top_level_occurrences([], _, []).
top_level_occurrences([Occurrence | Occurrences], All, TopLevel) :-
    Occurrence = occurrence(_, _, _, Handle),
    (   nested_in_another(Handle, All)
    ->  TopLevel = Rest
    ;   TopLevel = [Occurrence | Rest]
    ),
    top_level_occurrences(Occurrences, All, Rest).

nested_in_another(Handle, [occurrence(_, Layer, _, _) | Occurrences]) :-
    (   term_variables(Layer, Variables),
        variable_member(Handle, Variables)
    ->  true
    ;   nested_in_another(Handle, Occurrences)
    ).

variable_member(Variable, [Candidate | Candidates]) :-
    (   Variable == Candidate
    ->  true
    ;   variable_member(Variable, Candidates)
    ).

%!  occurrences_given(+TopLevel, -Condition)  the condition of the fast path
%   of a head: every top-level occurrence is given.

occurrences_given([Occurrence], Condition) :-
    !,
    occurrence_given(Occurrence, Condition).
occurrences_given([Occurrence | Occurrences], (Condition, Conditions)) :-
    occurrence_given(Occurrence, Condition),
    occurrences_given(Occurrences, Conditions).

%   An Id pattern is given when its handle is bound; an undetermined
%   occurrence when its variable is bound and not to an Id pattern of its
%   constructor whose handle is unbound. The Ids of a constructor whose
%   interning can be undetermined always have a shape.

occurrence_given(occurrence(id, _, _, Handle), nonvar(Handle)).
occurrence_given(occurrence(undetermined(IdName), _, Variable, _),
                 (nonvar(Variable), (Variable = Id -> nonvar(Handle) ; true))) :-
    compound_name_arguments(Id, IdName, [_, Handle]).

%!  occurrences_goal(+Occurrences, +Step, -Goal)  the conjunction of one step
%   over the occurrences, in the order given.

occurrences_goal([], _, true).
occurrences_goal([Occurrence], Step, Goal) :-
    !,
    occurrence_goal(Step, Occurrence, Goal).
occurrences_goal([Occurrence | Occurrences], Step, (Goal, Goals)) :-
    occurrence_goal(Step, Occurrence, Goal),
    occurrences_goal(Occurrences, Step, Goals).

%   The steps: `related` relates an occurrence to its layer; `related_if_given`
%   does so when it is given; `represented_if_ground` represents it when it is
%   not given and its layer is ground; `settled_unless_given` represents it at
%   the end of a head, where it must be settled; `represented_before_call`
%   interns a ground one and decides an undetermined one before a goal is
%   called.

occurrence_goal(related, occurrence(id, Layer, Id, _),
                hash_consing:intern(Layer, Id)).
occurrence_goal(related, occurrence(undetermined(_), Layer, Variable, _),
                hash_consing:represented(Layer, Variable)).
occurrence_goal(related_if_given, occurrence(id, Layer, Id, Handle),
                (nonvar(Handle) -> hash_consing:intern(Layer, Id) ; true)).
occurrence_goal(related_if_given, Occurrence,
                (Given -> hash_consing:represented(Layer, Variable) ; true)) :-
    Occurrence = occurrence(undetermined(_), Layer, Variable, _),
    occurrence_given(Occurrence, Given).
occurrence_goal(represented_if_ground, occurrence(id, Layer, Id, Handle),
                ((var(Handle), ground(Layer)) -> hash_consing:intern(Layer, Id) ; true)).
occurrence_goal(represented_if_ground, Occurrence,
                ((\+ Given, ground(Layer)) -> hash_consing:represented(Layer, Variable) ; true)) :-
    Occurrence = occurrence(undetermined(_), Layer, Variable, _),
    occurrence_given(Occurrence, Given).
occurrence_goal(settled_unless_given, occurrence(id, Layer, Id, Handle),
                (var(Handle) -> hash_consing:intern(Layer, Id) ; true)).
occurrence_goal(settled_unless_given, Occurrence,
                (Given -> true ; hash_consing:represented_settled(Layer, Variable))) :-
    Occurrence = occurrence(undetermined(_), Layer, Variable, _),
    occurrence_given(Occurrence, Given).
occurrence_goal(represented_before_call, occurrence(id, Layer, Id, _),
                (ground(Layer) -> hash_consing:intern(Layer, Id) ; true)).
occurrence_goal(represented_before_call, occurrence(undetermined(_), Layer, Variable, _),
                hash_consing:represented(Layer, Variable)).

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
    occurrences_goal(BottomUp, related, Inserts),
    occurrences_goal(BottomUp, represented_before_call, Settled),
    occurrences_goal(TopDown, related, Finished),
    conjoined([Inserts, Called], Fast),
    conjoined([Settled, Called, Finished], General).

%!  terms_variables(+Occurrences, -Variables)  the variables of the
%   occurrences' layers other than their own Handles.

terms_variables(Occurrences, Variables) :-
    occurrences_terms(Occurrences, Terms),
    term_variables(Terms, All),
    occurrences_handles(Occurrences, Handles),
    variables_without(All, Handles, Variables).

occurrences_terms([], []).
occurrences_terms([occurrence(_, Layer, _, _) | Occurrences], [Layer | Terms]) :-
    occurrences_terms(Occurrences, Terms).

occurrences_handles([], []).
occurrences_handles([occurrence(_, _, _, Handle) | Occurrences], [Handle | Handles]) :-
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
    (   listed_occurs(Term, File)
    ->  throw(error(domain_error(term_without_rewritten_constructor, Term),
                    context(hash_consing:rewritten/1, Place)))
    ;   true
    ).

listed_occurs(Term, File) :-
    compound(Term),
    !,
    compound_name_arity(Term, Name, Arity),
    (   registered_constructor(File, Name, Arity)
    ->  true
    ;   arg(_, Term, Argument),
        listed_occurs(Argument, File)
    ).
listed_occurs(Term, File) :-
    atom(Term),
    registered_constructor(File, Term, 0).

%   ---- the hook, last, so that this file's own clauses are read before it
%   is active ----

:- multifile user:term_expansion/2.
:- dynamic user:term_expansion/2.

user:term_expansion(Source, Rewritten) :-
    hash_consing:source_rewritten(Source, Rewritten).
