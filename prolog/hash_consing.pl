:- module(hash_consing,
          [ intern/2,               % ?Term, ?Id
            represented/2,          % ?Layer, ?Representation
            is_id/1,                % +Value
            externalized/2,         % +TermWithIds, -External
            internalized/3,         % +Templates, +External, -TermWithIds
            declared/1,             % +Templates
            rewritten/1,            % +Templates
            rewritten/2,            % +Templates, +Options
            store_property/1,       % ?Property
            store_growth_bounded/1  % +Bytes
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

A LAYER POSITION holds a layer, not a representation: in a file that opts
in, the term written there keeps its own constructor as a plain term and
only its arguments are rewritten. The first argument of `represented/2` is
one; `rewritten/2`'s option `layer_arguments` names more, in the heads and
goals of the file, for a predicate of a module that does not opt in and
hands out or takes the plain layer of a listed constructor (a reader of one
layer). A variable there stays a variable.

`:- hash_consing:rewritten(Templates).` OPTS A FILE IN (user ruling,
2026-09-17: opt-in per file, the constructors passed to the directive, no
setting). It declares the templates as `declared/1` does, and every clause
read after it in that file, included files counted, has each occurrence of a
constructor of the list rewritten as below, the direction of each call
decided at run time, so the file is written as the program that does not
intern and needs no mode declaration. Several directives in one file add up,
each declaring whole lists. An empty list rewrites nothing. The library
checks no consistency between files: files that pass one constructor to each
other must both list it, which the user arranges (user ruling, 2026-09-17).
SHARE ONE DIRECTIVE BY `include/1`: keep the directive in one file that every
file handing these terms to another includes; an included directive opts in
the file that includes it. A file left out fails silently (the FIXME below).

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
               neither). An Id occurrence over variables that occur once in
               the clause is unread: its Id pattern alone is passed, and
               after the call only its handle is checked
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
order see `'__hash_consed_Name/Arity'(Handle)`; the standard order of two Ids
depends on the history of insertions into the store, not on their terms.
Code that reads structure calls `externalized/2` first, and code that builds
an instance with them calls `internalized/3` after; an instance that must
be interned and is left uninterned fails to unify at every rewritten
position. Using an Id as an
opaque key, whose result does not depend on the order (an assoc key, a sort
to remove duplicates), is fine.

THE STORE BELONGS TO THE PROCESS. The store and the spellings of the shapes
are two tries made when this module is first loaded and kept in the fact
`process_stores/2`, so every thread and every engine interns into the same
store and reads the same Ids, with nothing to install. Reloading the module
keeps them. A lookup that finds its key with its handle written back takes no
lock; every write to the store, a value still `pending` settled included, is
made under a mutex. The Prolog flag `hash_consing_store_limit`, `infinite`
by default, bounds the bytes of the store: an insertion that would grow it
past the limit raises `resource_error(hash_consing_store)`, the way the
stack and table limits do, and the store stays as it was.
`store_growth_bounded/1` bounds instead what one thread adds to the store
from the call on, the way the stack and table limits bound one thread, so a
thread that shares the store with others, or finds it already full of what
earlier work interned, is charged with its own insertions only. A
declaration, an insertion into the store and a new spelling each take a mutex
(`hash_consing_templates`, `hash_consing_store`, `hash_consing_spellings`)
and look again under it before they write. `store_property/1` reads the size
of the store.

AN ID IS NEVER FREED NOR REUSED. The store only grows: an Id stays valid, and
stands for the same term, until the process ends. Two Ids are `==` exactly
when the terms they stand for are `==`, so an Id is a key of its term.

AN INTERNED TERM IS A VALUE, NOT A CELL. `intern/2` stores a copy of the
term as it is at the call: a later `setarg/3` or `nb_setarg/3` on the term
that was interned, or on a layer read back from an Id, changes that copy
only, never the store, and interning the old value again answers the same
Id. So a mutable cell (a thunk, a memory cell updated in place) must stay
outside the store; interning it freezes its value at that moment. An Id
itself must never be mutated: an Id whose handle is set to another Id's
handle is that other Id, and one set to any other integer crashes the
process (the FIXME below on `trie_term/2`).

THIS MODULE REFLECTS ON SOURCE CLAUSES with `=..` while a file loads, a
mechanical boundary; nothing here chooses behaviour at run time by
reflection, and no closure is handed to another module.

FIXME: `trie_term/2` on an integer that is no node of the store crashes the
process with a segmentation fault (measured 2026-09-14 on `trie_term(42,
_)`); a forged `'__hash_consed_apply/2'(42)` reaches it. Only a bug makes
such a value. Candidate fix: none in the trie API; the assertz backends of
the benchmark raise instead, at the costs recorded there.

FIXME: an Id written into a clause while the file loads
is a handle of this process. A file must be loaded from source, never
`qcompile`d nor saved in a state.

FIXME: a file that uses a constructor another file
interns, without listing it, passes its instances uninterned; the rewritten
positions of the other file then fail to unify, silently. The library does
not check it; one directive shared by `include/1` (above) avoids it.
*/

:- use_module(library(error), [must_be/2]).
:- use_module(library(lists), [reverse/2, member/2]).

:- initialization(stores_created).

%!  stores_created
%
%   The store and the spellings of the shapes, two tries of the process,
%   made unless an earlier load of this module made them.

:- dynamic process_stores/2.

stores_created :-
    (   process_stores(_, _)
    ->  true
    ;   trie_new(Store),
        trie_new(Spellings),
        assertz(process_stores(Store, Spellings))
    ).

%!  store_property(?Property) is nondet.
%
%   A property of the store: `ids(Count)`, the number of terms interned;
%   `nodes(Count)`, the number of nodes of its trie; `bytes(Bytes)`, the
%   memory the trie takes. The spellings of the shapes are not counted.

store_property(ids(Count)) :-
    process_stores(Store, _),
    trie_property(Store, value_count(Count)).
store_property(nodes(Count)) :-
    process_stores(Store, _),
    trie_property(Store, node_count(Count)).
store_property(bytes(Bytes)) :-
    process_stores(Store, _),
    trie_property(Store, size(Bytes)).

%   ---- the relation ----

%!  intern(?Term, ?Id)
%
%   Id is the Id of the ground term Term.

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

%!  upserted(+Term, ?Id)
%
%   When a template of Term's constructor matches it, insert Term unless it is
%   stored, and answer its Id; fail, inserting nothing, when none does.

upserted(Term, Id) :-
    process_stores(Trie, _),
    trie_lookup(Trie, Term, Handle),
    Handle \== pending,
    !,
    stored_id(Term, Handle, Id).
upserted(Term, Id) :-
    (   ground(Term)
    ->  true
    ;   throw(error(instantiation_error, context(hash_consing:intern/2, Term-Id)))
    ),
    functor(Term, Name, Arity),
    templates_known(Name, Arity, hash_consing:intern/2, Templates, Kind),
    (   Kind == root_only
    ->  true
    ;   first_template_recorded(Templates, Term, Structure)
    ),
    process_stores(Trie, _),
    (   trie_lookup(Trie, Term, Found),
        Found \== pending
    ->  Handle = Found
    ;   with_mutex(hash_consing_store, handle_inserted(Trie, Term, Handle))
    ),
    id_built(Name, Arity, Kind, Structure, Handle, Id).

%   stored_id(+Term, +Handle, ?Id): the Id of a term found in the store
%   with its handle written back. A stored term is ground and was declared,
%   and the first template that matched it when it was inserted still does,
%   so only the shape is computed again.

stored_id(Term, Handle, Id) :-
    functor(Term, Name, Arity),
    constructor_templates(Name, Arity, Templates, Kind),
    (   Kind == root_only
    ->  known_id_name(Name, Arity, IdName),
        compound_name_arguments(Id, IdName, [Handle])
    ;   first_template_recorded(Templates, Term, Structure),
        id_built(Name, Arity, Kind, Structure, Handle, Id)
    ).

%   handle_inserted(+Trie, +Term, -Handle): Term looked up again and, when it
%   is still absent, inserted, under the mutex `hash_consing_store`. Two
%   threads that share the store and both miss Term would otherwise both
%   insert it, and the second trie_insert/4 raises
%   `permission_error(modify, trie_key, Term)` (measured 2026-09-30: eight
%   threads interning the same 20000 terms raised in 5 of 5 runs). A lookup
%   that finds Term with its handle written back takes no mutex; a value
%   still `pending`, written by an insertion in progress in another thread or
%   left by an interrupted one, is settled here, under the mutex, so that only
%   the thread holding it writes to the store.

handle_inserted(Trie, Term, Handle) :-
    (   trie_lookup(Trie, Term, Found)
    ->  settled_handle(Trie, Term, Found, Handle)
    ;   store_within_limit(Trie),
        thread_growth_within_budget(Trie),
        trie_property(Trie, node_count(NodesBefore)),
        sig_atomic(inserted(Trie, Term, Handle)),
        thread_growth_counted(Trie, NodesBefore)
    ).

%!  store_within_limit(+Trie)
%
%   Raises `resource_error(hash_consing_store)` when the Prolog flag
%   `hash_consing_store_limit` is a number of bytes and the store takes more.
%   Measuring the bytes walks the whole trie (20 ms at 200,000 terms,
%   measured 2026-10-01), its node count does not, so the bytes are
%   estimated from the node count and the bytes per node of the last
%   measurement, and measured again only when the estimate passes the limit
%   or the nodes have doubled since; only a measurement raises.

:- create_prolog_flag(hash_consing_store_limit, infinite, [type(term), keep(true)]).

store_within_limit(Trie) :-
    current_prolog_flag(hash_consing_store_limit, Limit),
    (   Limit == infinite
    ->  true
    ;   must_be(positive_integer, Limit),
        trie_property(Trie, node_count(Nodes)),
        bytes_per_node(Trie, Nodes, MeasuredNodes, MeasuredBytes),
        (   Nodes * MeasuredBytes =< Limit * MeasuredNodes
        ->  true
        ;   trie_property(Trie, size(Bytes)),
            flag(hash_consing_measured_nodes, _, Nodes),
            flag(hash_consing_measured_bytes, _, Bytes),
            (   Bytes > Limit
            ->  format(atom(Measured), 'the store takes ~D bytes, the limit is ~D', [Bytes, Limit]),
                throw(error(resource_error(hash_consing_store),
                            context(hash_consing:intern/2, Measured)))
            ;   true
            )
        )
    ).

%   bytes_per_node(+Trie, +Nodes, -MeasuredNodes, -MeasuredBytes): the nodes
%   and bytes of the last measurement of the store, measured again when
%   there is none or the nodes have doubled since; their ratio estimates the
%   bytes of a node.

bytes_per_node(Trie, Nodes, MeasuredNodes, MeasuredBytes) :-
    flag(hash_consing_measured_nodes, KnownNodes, KnownNodes),
    flag(hash_consing_measured_bytes, KnownBytes, KnownBytes),
    (   KnownNodes > 0,
        Nodes < 2 * KnownNodes
    ->  MeasuredNodes = KnownNodes,
        MeasuredBytes = KnownBytes
    ;   trie_property(Trie, size(Bytes)),
        MeasuredNodes is max(Nodes, 1),
        MeasuredBytes = Bytes,
        flag(hash_consing_measured_nodes, _, MeasuredNodes),
        flag(hash_consing_measured_bytes, _, MeasuredBytes)
    ).

%!  store_growth_bounded(+Bytes)
%
%   From now on, this thread may grow the store by Bytes at most; `infinite`
%   lifts the bound. Once the nodes this thread inserted since the call take
%   more than Bytes, its next insertion raises
%   `error(resource_error(hash_consing_store), context(hash_consing:intern/2,
%   Message))`, Message stating the bytes added and the budget, the error
%   the flag `hash_consing_store_limit` raises. A term already in the store
%   costs nothing: interning it again adds no node, is not counted, and is
%   answered even past the budget. Only this thread's own insertions
%   count, measured as the nodes each one adds under the store's mutex, so
%   threads that share the store do not charge each other, and what the
%   store held before the call does not count. A thread created later inherits the bound with a count
%   of its own from zero, as it inherits `stack_limit` and `table_space`.
%   Bytes are estimated from the nodes as for the flag
%   `hash_consing_store_limit`. The bound lives in the Prolog flag
%   `hash_consing_growth_budget`.

:- create_prolog_flag(hash_consing_growth_budget, infinite, [type(term), keep(true)]).

store_growth_bounded(Bytes) :-
    (   Bytes == infinite
    ->  true
    ;   must_be(positive_integer, Bytes)
    ),
    set_prolog_flag(hash_consing_growth_budget, Bytes),
    nb_setval(hash_consing_growth_added, 0).

%   thread_growth_within_budget(+Trie): the nodes this thread inserted since
%   its budget was set take no more than the budget.

thread_growth_within_budget(Trie) :-
    current_prolog_flag(hash_consing_growth_budget, Bytes),
    (   Bytes == infinite
    ->  true
    ;   thread_growth_added(Added),
        trie_property(Trie, node_count(Nodes)),
        bytes_per_node(Trie, Nodes, MeasuredNodes, MeasuredBytes),
        (   Added * MeasuredBytes =< Bytes * MeasuredNodes
        ->  true
        ;   Spent is Added * MeasuredBytes // MeasuredNodes,
            format(atom(Measured),
                   'this thread grew the store by about ~D bytes, its budget is ~D',
                   [Spent, Bytes]),
            throw(error(resource_error(hash_consing_store),
                        context(hash_consing:intern/2, Measured)))
        )
    ).

%   thread_growth_added(-Added): the nodes this thread inserted since its
%   budget was set; zero in a thread that inherited the budget and has not
%   inserted yet.

thread_growth_added(Added) :-
    (   nb_current(hash_consing_growth_added, Added)
    ->  true
    ;   Added = 0
    ).

%   thread_growth_counted(+Trie, +NodesBefore): the nodes the insertion just
%   made, the store's nodes now less NodesBefore, added to this thread's
%   count when it has a budget. Called under the store's mutex, right after
%   the insertion, so no other thread's nodes are counted.

thread_growth_counted(Trie, NodesBefore) :-
    current_prolog_flag(hash_consing_growth_budget, Bytes),
    (   Bytes == infinite
    ->  true
    ;   thread_growth_added(AddedBefore),
        trie_property(Trie, node_count(Nodes)),
        Added is AddedBefore + Nodes - NodesBefore,
        nb_setval(hash_consing_growth_added, Added)
    ).

%   inserted(+Trie, +Term, -Handle): the insertion and the write-back of the
%   key's own handle as its value, run under `sig_atomic/1` by
%   handle_inserted/3, so
%   that a signal (a `call_with_time_limit/2` expiring) waits until both are
%   done. `call_with_inference_limit/3` is no signal: its limit can still
%   fall between the two and leave the value `pending` (measured 2026-09-27:
%   interning a fresh two-argument term under a limit of 9 inferences left it
%   `pending`, and the next lookup handed `pending` to `trie_term/2`, which
%   raised `type_error(address, pending)`). settled_handle/4 repairs such a
%   key at its next lookup.

inserted(Trie, Term, Handle) :-
    trie_insert(Trie, Term, pending, Handle),
    trie_update(Trie, Term, Handle).

%   settled_handle(+Trie, +Term, +Found, -Handle): the handle of Term's node,
%   Found when the value was written back, and otherwise, when an
%   interrupted insertion left `pending`, the node's own handle, read with
%   `'$trie_gen_node'/3` (SWI-Prolog's generator of a trie's keys with their
%   nodes, here with the key bound) and written back. The repair may itself
%   be interrupted between its two steps; the key then stays `pending` and
%   is repaired at its next lookup.

settled_handle(Trie, Term, pending, Handle) :-
    !,
    '$trie_gen_node'(Trie, Term, Handle),
    trie_update(Trie, Term, Handle).
settled_handle(_, _, Handle, Handle).

%!  represented(?Layer, ?Representation)
%
%   Representation represents Layer, a constructor applied to represented
%   arguments: its Id when a template of the constructor matches it, Layer
%   itself otherwise.
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

representation_made(_, _, _, _, Layer, Representation) :-
    ground(Layer),
    !,
    (   upserted(Layer, Id)
    ->  Representation = Id
    ;   Representation = Layer
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

%!  represented_settled(+Layer, ?Representation)
%
%   Represented/2 at the end of a rewritten head, where rule (1) of the module
%   comment leaves no Id pattern with an unbound handle: such a pattern raises
%   an instantiation error.

represented_settled(Layer, Representation) :-
    represented(Layer, Representation),
    (   id_parts(Representation, _, _, Handle),
        var(Handle)
    ->  throw(error(instantiation_error, context(hash_consing:represented/2, Layer)))
    ;   true
    ).

%!  is_id(+Value)
%
%   Value is an Id: an Id functor this process made, applied to a bound
%   handle. The handle is the last argument of both Id arities, so the test
%   reads it directly instead of through id_parts/4: lambda_jit's
%   term_weight.pl calls it once per node it weighs.

is_id(Value) :-
    compound(Value),
    compound_name_arity(Value, IdName, Arity),
    id_constructor(IdName, _, _),
    arg(Arity, Value, Handle),
    nonvar(Handle).

%!  id_parts(+Value, -IdName, -Shape, -Handle)
%
%   Value is an Id or an Id pattern: its functor is one id_name/3 made, which
%   the first argument index of id_constructor/3 finds without scanning the
%   name (the prefix test it replaces took 30 percent of a lambda_jit read,
%   2026-09-26). Shape is `none` for a constructor without a shape. Fails on
%   any other value.

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

%!  id_built(+Name, +Arity, +Kind, +Structure, ?Handle, -Id)
%
%   The Id, or the Id pattern, of the constructor with the handle Handle: no
%   shape when Kind is `root_only`, an unbound shape when Structure is
%   `unknown`, and otherwise the spelling of Structure.

id_built(Name, Arity, Kind, Structure, Handle, Id) :-
    id_name(Name, Arity, IdName),
    (   Kind == root_only
    ->  compound_name_arguments(Id, IdName, [Handle])
    ;   Structure == unknown
    ->  compound_name_arguments(Id, IdName, [_, Handle])
    ;   structure_spelled(Structure, Shape),
        compound_name_arguments(Id, IdName, [Shape, Handle])
    ).

%!  id_name(+Name, +Arity, -IdName)
%
%   The functor name of the Ids of the constructor Name/Arity, remembered once
%   made, in both directions.

:- dynamic known_id_name/3.             % known_id_name(Name, Arity, IdName)
:- dynamic id_constructor/3.            % id_constructor(IdName, Name, Arity)

id_name(Name, Arity, IdName) :-
    (   known_id_name(Name, Arity, Known)
    ->  IdName = Known
    ;   with_mutex(hash_consing_templates, id_name_made(Name, Arity, IdName))
    ).

%   id_name_made(+Name, +Arity, -IdName): the name looked up again under the
%   mutex `hash_consing_templates`, and made when it is still unknown.
%   id_constructor/3 is asserted before known_id_name/3, so a thread that
%   finds the name without the mutex also finds the fact id_parts/4 reads.

id_name_made(Name, Arity, IdName) :-
    (   known_id_name(Name, Arity, Known)
    ->  IdName = Known
    ;   format(atom(Made), '__hash_consed_~w/~d', [Name, Arity]),
        assertz(id_constructor(Made, Name, Arity)),
        assertz(known_id_name(Name, Arity, Made)),
        IdName = Made
    ).

%   ---- the templates of a constructor ----

%   A TEMPLATE IS KEPT PARSED, `template(Name/Arity, Arguments)` with one of
%   `ignored` (for `_`), `root` (for `*`) or a nested template per argument,
%   ground, so that two declarations of a constructor compare with `==`.

:- dynamic constructor_templates/4.     % constructor_templates(Name, Arity, Templates, Kind)

%!  declared(+Templates)
%
%   The constructors of the list declared for this process, each with its
%   templates in the order of the list.

declared(Templates) :-
    templates_declared(Templates, hash_consing:declared/1, _).

%!  templates_known(+Name, +Arity, +Context, -Templates, -Kind)
%
%   The declared templates of the constructor, and `root_only` or `shaped`;
%   raises when the constructor has none.

templates_known(Name, Arity, Context, Templates, Kind) :-
    (   constructor_templates(Name, Arity, Templates, Kind)
    ->  true
    ;   throw(error(existence_error(templates, Name/Arity), context(Context, _)))
    ).

%!  templates_declared(+Templates, +Context, -Constructors)
%
%   The list parsed and grouped by constructor, in the order of first
%   appearance; every group checked before any is registered; Constructors the
%   `Name/Arity` of the groups. Raises, registering nothing, on a malformed or
%   unreachable template and on a constructor already declared with another
%   list.

templates_declared(Templates, Context, Constructors) :-
    must_be(list, Templates),
    templates_parsed(Templates, Context, Parsed),
    parsed_constructors(Parsed, [], Reversed),
    reverse(Reversed, Constructors),
    constructors_groups(Constructors, Parsed, Groups),
    with_mutex(hash_consing_templates, groups_declared(Groups, Context)).

%   groups_declared(+Groups, +Context): the groups checked against the lists
%   already declared, then registered, as one step under the mutex
%   `hash_consing_templates`. Two threads declaring a constructor at once
%   would otherwise both find it undeclared and both register it (measured
%   2026-09-30: eight threads declaring the same 2000 constructors left 3924
%   registrations and 3631 Id names, and is_id/1 answered once for each Id
%   name of its constructor, since id_parts/4 reads them).

groups_declared(Groups, Context) :-
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

%!  templates_reachable(+Written, +Templates, +Earlier, +Context)
%
%   No template is always taken first by one template before it.

templates_reachable([], [], _, _).
templates_reachable([Template | Written], [Parsed | Templates], Earlier, Context) :-
    (   member(EarlierTemplate, Earlier),
        template_covers(EarlierTemplate, Parsed)
    ->  throw(error(domain_error(reachable_template, Template), context(Context, _)))
    ;   templates_reachable(Written, Templates, [Parsed | Earlier], Context)
    ).

%!  template_covers(+Covering, +Covered)
%
%   Every term Covered matches, Covering matches too.

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

%!  templates_parsed(+Templates, +Context, -Pairs)
%
%   Each template paired with its parsed form, `Template-Parsed`.

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

%!  templates_written(+Templates, -Written)
%
%   Parsed templates written back as a user writes them, for an error to show.

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

%!  value_classified(+Templates, +Value, -Class, -Structure)
%
%   Class is `must_intern` when a template matches every term Value stands
%   for, `must_not_intern` when no template matches any, `undetermined`
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

%!  first_template_recorded(+Templates, +Term, -Structure)
%
%   What the first template that matches the ground Term records; fails when
%   none does.

first_template_recorded([Template | Templates], Term, Structure) :-
    template_relation(Template, Term, Relation, Descriptions),
    (   Relation == instance
    ->  Structure = Descriptions
    ;   first_template_recorded(Templates, Term, Structure)
    ).

%!  template_relation(+Template, +Value, -Relation, -Descriptions)
%
%   Whether every term Value stands for matches the template (`instance`),
%   none does (`disjoint`) or some do (`overlap`), and what the template
%   records on them. Value's own root is the template's constructor.

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

%!  value_root(+Value, -Root)
%
%   The root constructor of the term Value stands for, `Name/Arity`, read off
%   an Id's functor name without a lookup; `open` for a variable, `other` for
%   a number or a string.

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

%!  value_view(+Value, -View)
%
%   `layer(Name/Arity, Arguments)`, the root and the arguments of the term
%   Value stands for, an Id's read from the store and open while its handle is
%   unbound; `open` for a variable; `other` for a number or a string.

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

%!  structure_spelled(+Structure, -Atom)
%
%   The shape atom of a structure, remembered in the trie of spellings so that
%   it is built once.

structure_spelled(Structure, Atom) :-
    process_stores(_, Spellings),
    (   trie_lookup(Spellings, Structure, Known)
    ->  Atom = Known
    ;   with_mutex(hash_consing_spellings, spelling_inserted(Spellings, Structure, Atom))
    ).

%   spelling_inserted(+Spellings, +Structure, -Atom): the spelling looked up
%   again and, when it is still absent, made and inserted, under the mutex
%   `hash_consing_spellings`. Two threads that both miss a structure would
%   otherwise both insert it, and the second trie_insert/3 fails, which
%   fails its interning (measured 2026-09-30: eight threads spelling the
%   same 2000 shapes).

spelling_inserted(Spellings, Structure, Atom) :-
    (   trie_lookup(Spellings, Structure, Known)
    ->  Atom = Known
    ;   structure_atom(Structure, Atom),
        trie_insert(Spellings, Structure, Atom)
    ).

%!  structure_atom(+Structure, -Atom)
%
%   The spelling: descriptions joined by commas, `-` for `other`, `Name/Arity`
%   and, in parentheses, what is below.

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

%!  externalized(+TermWithIds, -External)
%
%   Every Id replaced by its term, recursively.

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

%!  internalized(+Templates, +External, -TermWithIds)
%
%   The templates declared as declared/1 declares them, then every instance of
%   their constructors represented, bottom up: its Id when a template matches
%   it, the plain term otherwise; an Id is kept as it is.

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
        ->  (   upserted(Layer, Id)
            ->  Internal = Id
            ;   Internal = Layer
            )
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

%!  rewritten(+Templates)
%
%   The file being loaded opts in for the constructors whose templates are in
%   the list; several calls add up. The same as `rewritten(Templates, [])`.

%!  rewritten(+Templates, +Options)
%
%   rewritten/1 with Options, of which there is one:
%
%     - layer_arguments(Skeletons)
%       Each skeleton is a head or goal, `Name(A1, ..., An)`, with the atom
%       `layer` at the argument positions that hold a LAYER and `_`
%       elsewhere. In every head and body goal of the file with that name
%       and arity, the term at a layer position keeps its own constructor as
%       written, a plain term, and only its arguments are rewritten, as
%       hash_consing:represented/2 reads its first argument. This is how a
%       file that opts in calls a predicate of a file that does not, one
%       that hands out or takes the plain layer of a listed constructor.

:- dynamic registered_constructor/3.     % registered_constructor(SourceFile, Name, Arity)
:- dynamic registered_layer_positions/4. % registered_layer_positions(SourceFile, Name, Arity, Positions)

rewritten(Templates) :-
    rewritten_with_options(Templates, [], hash_consing:rewritten/1).

rewritten(Templates, Options) :-
    rewritten_with_options(Templates, Options, hash_consing:rewritten/2).

rewritten_with_options(Templates, Options, Context) :-
    must_be(list, Templates),
    must_be(list, Options),
    options_checked(Options, Context, Layered),
    (   prolog_load_context(source, File)
    ->  true
    ;   throw(error(context_error(nodirective, Context), _))
    ),
    templates_declared(Templates, Context, Constructors),
    constructors_registered(Constructors, File),
    layered_registered(Layered, File, Context).

options_checked([], _, []).
options_checked([Option | Options], Context, Layered) :-
    (   Option = layer_arguments(Skeletons),
        is_list(Skeletons)
    ->  skeletons_read(Skeletons, Context, Layered, Rest),
        options_checked(Options, Context, Rest)
    ;   throw(error(domain_error(rewritten_option, Option), context(Context, _)))
    ).

%   skeletons_read(+Skeletons, +Context, -Layered, ?Rest): each skeleton
%   read as `layered(Name, Arity, Positions)`, its layer positions, in front
%   of Rest.

skeletons_read([], _, Rest, Rest).
skeletons_read([Skeleton | Skeletons], Context, [layered(Name, Arity, Positions) | Layered], Rest) :-
    (   compound(Skeleton),
        compound_name_arguments(Skeleton, Name, Arguments),
        layer_markers(Arguments, 1, Positions),
        Positions \== []
    ->  length(Arguments, Arity)
    ;   throw(error(domain_error(layer_skeleton, Skeleton), context(Context, _)))
    ),
    skeletons_read(Skeletons, Context, Layered, Rest).

%   layered_registered(+Layered, +File, +Context): the layer positions
%   recorded for File; a second skeleton of the same name and arity in one
%   file must give the same positions.

layered_registered([], _, _).
layered_registered([layered(Name, Arity, Positions) | Layered], File, Context) :-
    (   registered_layer_positions(File, Name, Arity, Known)
    ->  (   Known == Positions
        ->  true
        ;   throw(error(permission_error(reconfigure, layer_arguments, Name/Arity),
                        context(Context, _)))
        )
    ;   assertz(registered_layer_positions(File, Name, Arity, Positions))
    ),
    layered_registered(Layered, File, Context).

%   layer_markers(+Arguments, +Position, -Positions): the positions, from
%   Position on, of the arguments that are the atom `layer`; any other
%   argument must be a variable.

layer_markers([], _, []).
layer_markers([Argument | Arguments], Position, Positions) :-
    Next is Position + 1,
    (   Argument == layer
    ->  Positions = [Position | Rest]
    ;   var(Argument)
    ->  Positions = Rest
    ),
    layer_markers(Arguments, Next, Rest).

constructors_registered([], _).
constructors_registered([Name/Arity | Constructors], File) :-
    (   registered_constructor(File, Name, Arity)
    ->  true
    ;   assertz(registered_constructor(File, Name, Arity))
    ),
    constructors_registered(Constructors, File).

%   ---- the rewrite ----

%!  source_rewritten(+Source, -Rewritten)
%
%   The rewrite of one term read from a file that opted in; fails, leaving the
%   term to SWI-Prolog, otherwise.

source_rewritten(Source, _) :-
    var(Source),
    !,
    fail.
source_rewritten(end_of_file, _) :-
    !,
    prolog_load_context(source, File),
    prolog_load_context(file, File),
    retractall(registered_constructor(File, _, _)),
    retractall(registered_layer_positions(File, _, _, _)),
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

%!  rule_rewritten(+Head, +Body, +File, -Rewritten)
%
%   The head's occurrences scheduled around the rewritten body.

rule_rewritten(Qualifier:Head0, Body0, File, (Qualifier:Head :- Body)) :-
    !,
    plain_rule_rewritten(Head0, Body0, File, Head, Body).
rule_rewritten(Head0, Body0, File, (Head :- Body)) :-
    plain_rule_rewritten(Head0, Body0, File, Head, Body).

plain_rule_rewritten(Head0, Body0, File, Head, Body) :-
    file_layer_positions(Head0, File, Positions),
    arguments_of_abstracted(Head0, Positions, File, Head, Occurrences),
    term_singletons(Head0-Body0, Singletons),
    body_rewritten(Body0, rewriting(File, Singletons), RewrittenBody),
    head_scheduled(Occurrences, Head-RewrittenBody, RewrittenBody, Body).

%!  arguments_of_abstracted(+Callable0, +LayerPositions, +File, -Callable, -Occurrences)
%
%   The arguments of a head or a goal abstracted (its own functor is a
%   predicate and is left alone; an argument at one of LayerPositions keeps
%   its own constructor), the ground occurrences represented now, and
%   the others listed bottom up as
%   `occurrence(Class, Layer, Representation, Handle)`: Class `id` for an
%   occurrence that must be interned, its Representation an Id pattern and
%   Handle that pattern's handle, and `undetermined(IdName)` for an
%   undetermined one, its Representation and its Handle the fresh variable
%   written where it stood. An occurrence that must not be interned is its
%   layer, written in place, and is not listed.

arguments_of_abstracted(Callable0, LayerPositions, File, Callable, Occurrences) :-
    compound(Callable0),
    !,
    compound_name_arguments(Callable0, Name, Arguments0),
    positioned_arguments_abstracted(Arguments0, 1, LayerPositions, File, Arguments, [], Reversed),
    compound_name_arguments(Callable, Name, Arguments),
    reverse(Reversed, BottomUp),
    occurrences_baked(BottomUp, Occurrences).
arguments_of_abstracted(Callable, _, _, Callable, []).

%   file_layer_positions(+Callable, +File, -Positions): the layer positions
%   File registered for Callable's name and arity (rewritten/2), none when
%   it registered none.

file_layer_positions(Callable, File, Positions) :-
    (   compound(Callable),
        compound_name_arity(Callable, Name, Arity),
        registered_layer_positions(File, Name, Arity, Registered)
    ->  Positions = Registered
    ;   Positions = []
    ).

%   positioned_arguments_abstracted(+Arguments0, +Position, +LayerPositions,
%   +File, -Arguments, +Reversed0, -Reversed): arguments_abstracted/5, the
%   argument at a layer position kept as a plain layer: its own
%   constructor as written, its arguments abstracted.

positioned_arguments_abstracted([], _, _, _, [], Reversed, Reversed).
positioned_arguments_abstracted([Argument0 | Arguments0], Position, LayerPositions, File,
                                [Argument | Arguments], Reversed0, Reversed) :-
    (   memberchk(Position, LayerPositions)
    ->  layer_abstracted(Argument0, File, Argument, Reversed0, Reversed1)
    ;   abstracted(Argument0, File, Argument, Reversed0, Reversed1)
    ),
    Next is Position + 1,
    positioned_arguments_abstracted(Arguments0, Next, LayerPositions, File,
                                    Arguments, Reversed1, Reversed).

layer_abstracted(Layer0, File, Layer, Reversed0, Reversed) :-
    (   compound(Layer0)
    ->  compound_name_arguments(Layer0, Name, Arguments0),
        arguments_abstracted(Arguments0, File, Arguments, Reversed0, Reversed),
        compound_name_arguments(Layer, Name, Arguments)
    ;   Layer = Layer0,
        Reversed = Reversed0
    ).

arguments_abstracted([], _, [], Reversed, Reversed).
arguments_abstracted([Argument0 | Arguments0], File, [Argument | Arguments], Reversed0, Reversed) :-
    abstracted(Argument0, File, Argument, Reversed0, Reversed1),
    arguments_abstracted(Arguments0, File, Arguments, Reversed1, Reversed).

%!  abstracted(+Term0, +File, -Term, +Reversed0, -Reversed)
%
%   Each occurrence of a listed constructor replaced by its representation in
%   the clause, its subterms first, the listed occurrences prepended as they
%   are met.

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

%!  occurrence_abstracted(+Name, +Arity, +Source, +Layer, +File, -Representation, +Reversed0, -Reversed)
%
%   AN OCCURRENCE IS CLASSIFIED (above) by its source pattern Source, and
%   written as an Id pattern, as its layer, or as a fresh variable.

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

%!  occurrences_baked(+BottomUp, -Remaining)
%
%   An occurrence whose layer is ground is represented while the file loads,
%   which binds its Id in the clause; bottom up, so a parent of baked
%   occurrences may become ground in turn.

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

%!  head_scheduled(+BottomUp, +Clause, +Body0, -Body)
%
%   The head row of THE REWRITE OF A CLAUSE (above). Clause is the
%   rewritten head paired with Body0, read only to find the occurrences whose
%   layer nothing reads.

head_scheduled([], _, Body, Body) :-
    !.
head_scheduled(BottomUp, Clause, Body0, (Condition -> Fast ; General)) :-
    reverse(BottomUp, TopDown),
    top_level_occurrences(BottomUp, BottomUp, TopLevel),
    occurrences_given(TopLevel, Condition),
    occurrences_read(TopDown, Clause-BottomUp, Read),
    occurrences_goal(Read, related, Lookups),
    occurrences_goal(TopDown, related_if_given, Settled),
    occurrences_goal(BottomUp, represented_if_ground, Inserted),
    occurrences_goal(BottomUp, settled_unless_given, Finished),
    conjoined([Lookups, Body0], Fast),
    conjoined([Settled, Inserted, Body0, Finished], General).

%!  conjoined(+Goals, -Conjunction)
%
%   The goals in order, `true` left out.

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

%   occurrences_read(+Occurrences, +Clause, -Read): the occurrences whose
%   layer the clause reads. A given Id's layer is looked up only to bind the
%   layer's arguments; an Id occurrence whose layer is its constructor over
%   variables that occur nowhere else in Clause (the head, the body and the
%   layers of the listed occurrences) binds nothing anyone reads, and is left
%   out of the fast path. Its Id pattern in the head already selects the
%   constructor and the shape. Every other occurrence is kept.

occurrences_read(Occurrences, Clause, Read) :-
    variables_occurring_more_than_once(Clause, Shared),
    occurrences_kept_when_read(Occurrences, Shared, Read).

occurrences_kept_when_read([], _, []).
occurrences_kept_when_read([Occurrence | Occurrences], Shared, Read) :-
    (   Occurrence = occurrence(id, Layer, _, _),
        layer_arguments(Layer, Arguments),
        unread_arguments(Arguments, Shared)
    ->  Read = Rest
    ;   Read = [Occurrence | Rest]
    ),
    occurrences_kept_when_read(Occurrences, Shared, Rest).

layer_arguments(Layer, Arguments) :-
    (   atom(Layer)
    ->  Arguments = []
    ;   compound_name_arguments(Layer, _, Arguments)
    ).

unread_arguments([], _).
unread_arguments([Argument | Arguments], Shared) :-
    var(Argument),
    \+ variable_member(Argument, Shared),
    unread_arguments(Arguments, Shared).

%   variables_occurring_more_than_once(+Term, -Shared): the variables of Term
%   that occur in it more than once.

variables_occurring_more_than_once(Term, Shared) :-
    term_singletons(Term, Singletons),
    term_variables(Term, Variables),
    variables_not_in(Variables, Singletons, Shared).

variables_not_in([], _, []).
variables_not_in([Variable | Variables], Excluded, Kept) :-
    (   variable_member(Variable, Excluded)
    ->  Kept = Rest
    ;   Kept = [Variable | Rest]
    ),
    variables_not_in(Variables, Excluded, Rest).

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

%!  occurrences_given(+TopLevel, -Condition)
%
%   The condition of the fast path of a head: every top-level occurrence is
%   given.

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

%!  occurrences_goal(+Occurrences, +Step, -Goal)
%
%   The conjunction of one step over the occurrences, in the order given.

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

%!  body_rewritten(+Body0, +Context, -Body)
%
%   Context is `rewriting(File, Singletons)`, Singletons the variables that
%   occur once in the source clause.
%
%   The control constructs rewritten inside, every other goal by
%   `goal_rewritten/3`.

body_rewritten(Goal, _, Goal) :-
    var(Goal),
    !.
body_rewritten((Left0, Right0), Context, (Left, Right)) :-
    !,
    body_rewritten(Left0, Context, Left),
    body_rewritten(Right0, Context, Right).
body_rewritten((Left0 ; Right0), Context, (Left ; Right)) :-
    !,
    body_rewritten(Left0, Context, Left),
    body_rewritten(Right0, Context, Right).
body_rewritten((Condition0 -> Then0), Context, (Condition -> Then)) :-
    !,
    body_rewritten(Condition0, Context, Condition),
    body_rewritten(Then0, Context, Then).
body_rewritten((Condition0 *-> Then0), Context, (Condition *-> Then)) :-
    !,
    body_rewritten(Condition0, Context, Condition),
    body_rewritten(Then0, Context, Then).
body_rewritten(\+ Goal0, Context, \+ Goal) :-
    !,
    body_rewritten(Goal0, Context, Goal).
body_rewritten(call(Goal0), Context, call(Goal)) :-
    !,
    body_rewritten(Goal0, Context, Goal).
body_rewritten(forall(Condition0, Action0), Context, forall(Condition, Action)) :-
    !,
    body_rewritten(Condition0, Context, Condition),
    body_rewritten(Action0, Context, Action).
body_rewritten(findall(Template, Goal0, Result), Context, findall(Template, Goal, Result)) :-
    !,
    context_file(Context, File),
    listed_absent(Template-Result, File, findall_template_or_result),
    body_rewritten(Goal0, Context, Goal).
body_rewritten(catch(Goal0, Catcher, Recovery0), Context, catch(Goal, Catcher, Recovery)) :-
    !,
    context_file(Context, File),
    listed_absent(Catcher, File, catch_catcher),
    body_rewritten(Goal0, Context, Goal),
    body_rewritten(Recovery0, Context, Recovery).
body_rewritten(hash_consing:Goal0, Context, hash_consing:Goal) :-
    templates_first(Goal0),
    !,
    templates_kept(Goal0, Context, Goal).
body_rewritten(hash_consing:Goal0, Context, hash_consing:Goal) :-
    layer_first(Goal0),
    !,
    goal_rewritten(Goal0, [1], Context, Goal).
body_rewritten(Qualifier:Goal0, Context, Qualifier:Goal) :-
    !,
    body_rewritten(Goal0, Context, Goal).
body_rewritten(Goal0, Context, Goal) :-
    templates_first(Goal0),
    prolog_load_context(module, Module),
    predicate_property(Module:Goal0, imported_from(hash_consing)),
    !,
    templates_kept(Goal0, Context, Goal).
body_rewritten(Goal0, Context, Goal) :-
    layer_first(Goal0),
    prolog_load_context(module, Module),
    predicate_property(Module:Goal0, imported_from(hash_consing)),
    !,
    goal_rewritten(Goal0, [1], Context, Goal).
body_rewritten(Goal0, Context, Goal) :-
    context_file(Context, File),
    file_layer_positions(Goal0, File, Positions),
    goal_rewritten(Goal0, Positions, Context, Goal).

%   templates_first(+Goal): Goal is a predicate of this library whose first
%   argument is a list of templates. The templates are data the library
%   reads, not terms to intern, so a call of it in an opted-in file keeps
%   them as written (templates_kept/3), and only its other arguments are
%   rewritten.

templates_first(internalized(_, _, _)).
templates_first(declared(_)).

templates_kept(Goal0, Context, Goal) :-
    compound_name_arguments(Goal0, Name, [Templates | Arguments]),
    compound_name_arguments(StandIn, Name, [Placeholder | Arguments]),
    goal_rewritten(StandIn, [], Context, Goal),
    Placeholder = Templates.

%   layer_first(+Goal): Goal is a predicate of this library whose first
%   argument is a layer, kept as a plain layer in an opted-in file.

layer_first(represented(_, _)).

context_file(rewriting(File, _), File).

%!  goal_rewritten(+Goal0, +LayerPositions, +Context, -Goal)
%
%   The body goal row of THE REWRITE OF A CLAUSE (above), the arguments at
%   LayerPositions kept as plain layers. An Id occurrence whose layer is its
%   constructor over variables that occur once in the source clause is
%   UNREAD: those variables are unbound at the call and nobody reads them
%   after it, so its Id pattern alone, which selects the constructor and the
%   shape, is all the goal needs. It is left out of the schedule; after the
%   call only its handle is checked, and an unbound handle is handed to
%   intern/2, which raises as it would have.

goal_rewritten(Goal0, LayerPositions, rewriting(File, Singletons), Goal) :-
    arguments_of_abstracted(Goal0, LayerPositions, File, Called, BottomUp),
    occurrences_partitioned(BottomUp, Singletons, Read, Unread),
    goal_scheduled(Read, Called, Scheduled),
    unread_checks(Unread, Checks),
    conjoined([Scheduled | Checks], Goal).

occurrences_partitioned([], _, [], []).
occurrences_partitioned([Occurrence | Occurrences], Singletons, Read, Unread) :-
    (   Occurrence = occurrence(id, Layer, _, _),
        layer_arguments(Layer, Arguments),
        Arguments \== [],
        singleton_arguments(Arguments, Singletons)
    ->  Unread = [Occurrence | UnreadRest],
        Read = ReadRest
    ;   Read = [Occurrence | ReadRest],
        Unread = UnreadRest
    ),
    occurrences_partitioned(Occurrences, Singletons, ReadRest, UnreadRest).

singleton_arguments([], _).
singleton_arguments([Argument | Arguments], Singletons) :-
    var(Argument),
    variable_member(Argument, Singletons),
    singleton_arguments(Arguments, Singletons).

unread_checks([], []).
unread_checks([occurrence(id, Layer, Id, Handle) | Occurrences],
              [(nonvar(Handle) -> true ; hash_consing:intern(Layer, Id)) | Checks]) :-
    unread_checks(Occurrences, Checks).

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

%!  terms_variables(+Occurrences, -Variables)
%
%   The variables of the occurrences' layers other than their own Handles.

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

%!  listed_absent(+Term, +File, +Place)
%
%   No listed constructor occurs in Term, a place the rewrite does not
%   schedule; raises otherwise.

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

%   The message of a constructor with no templates names the two ways to
%   give it some.

:- multifile prolog:error_message//1.

prolog:error_message(resource_error(hash_consing_store)) -->
    [ 'The hash_consing store passed the limit set by the flag'-[], nl,
      'hash_consing_store_limit, or this thread passed the growth budget'-[], nl,
      'set by hash_consing:store_growth_bounded/1; the store keeps every'-[], nl,
      'term interned so far.'-[]
    ].
prolog:error_message(existence_error(templates, Name/Arity)) -->
    [ 'No templates for the constructor ~q in this process.'-[Name/Arity], nl,
      'Declare them with hash_consing:declared/1, or list them in the'-[], nl,
      'hash_consing:rewritten/1 directive of the files that use them.'-[]
    ].
