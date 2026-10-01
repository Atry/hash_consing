# hash_consing

[![CI](https://github.com/Atry/hash_consing/actions/workflows/ci.yml/badge.svg)](https://github.com/Atry/hash_consing/actions/workflows/ci.yml)

Hash-consed terms for SWI-Prolog, and a load-time rewrite that makes a
program use them. A file is written as the program that does not intern and
names, by templates, the terms to intern: a term is interned when a template
of its constructor matches it, and stays a plain term otherwise. Every clause
read after the directive refers to the interned terms by Ids, each wrapping a
node handle of one trie, and the store is canonical: the same term has the
same Id.

## Install

```prolog
?- pack_install(hash_consing).
```

## Use

Keep the directive that names the terms to intern in a file of its own:

```prolog
% calculus_templates.pl
:- use_module(library(hash_consing), []).
:- hash_consing:rewritten([apply(lambda(_), _), lambda(_), variable(_)]).
```

and include it in every file that uses these terms:

```prolog
:- module(steps, [step/2, built/2]).
:- include(calculus_templates).

step(apply(lambda(Body), Argument), beta(Body, Argument)).

built(Function, Applied) :-
    Applied = apply(Function, variable(0)).
```

```prolog
:- module(redexes, [is_redex/1]).
:- include(calculus_templates).

is_redex(apply(lambda(_), _)).
```

Here an application is interned when its first argument is a lambda; any
other application stays a plain compound whose arguments are represented in
turn. The included directive opts in the file that includes it, so both
modules rewrite the same terms: when `built/2` in `steps` applies a lambda,
the application it makes is the Id that the head of `is_redex/1` in
`redexes` expects.

**Warning:** the rewrite is per file. A file rewrites only the terms its own
directive names, and the library checks nothing between files. A file that
receives interned terms without including the directive keeps plain terms
in its clauses, so its heads never unify with the Ids: the call fails,
silently, with no error. Write the directive once and include it everywhere.

A term that did not come through the rewrite crosses the boundary with
`hash_consing:internalized/3`, `hash_consing:externalized/2` turns Ids back
into terms, and `hash_consing:declared/1` declares templates at run time, for
constructors a program makes as it runs. The module comment of
[`prolog/hash_consing.pl`](prolog/hash_consing.pl) is the reference: the
relation `intern/2`, the Id and its shape, the templates, the rewrite of a
clause, the two rules for a file that opts in, and the known defects.

### Calling a module that hands out layers

A module that does not opt in may read an Id one layer at a time and hand
out that layer, a plain compound whose arguments are Ids. In a file that
opts in, a plain `slot(Index)` written in a call would be rewritten into an
Id pattern and would not match it. `rewritten/2` names the argument
positions that hold such a layer: there the constructor stays as written
and only its arguments are rewritten. The first argument of
`hash_consing:represented/2` is such a position already.

```prolog
:- hash_consing:rewritten([slot(_), link(_, _)],
                          [layer_arguments([stored_layer(_, layer)])]).

slot_read(Slot, Index) :-
    stored_layer(Slot, slot(Index)).            % slot(Index) is a plain layer
linked_index(Link, Index) :-
    stored_layer(Link, link(slot(Index), _)).   % the inner slot/1 is an Id
```

## Templates are patterns

What is interned is chosen by patterns, not by constructors. A template is
written like the clause heads it serves: a constructor applied, at each
argument position, to `_` (any argument), `*` (any argument, its root
constructor recorded) or a nested template (an argument with the nested
template's constructor, whose arguments match the nested template's). A
constructor may have several templates. They are tried in the order of the
list, the first that matches a term is its template, and a term that none
matches is not interned. From
[`test/hash_consing_fixtures/patterns_templates.pl`](test/hash_consing_fixtures/patterns_templates.pl):

```prolog
:- use_module(library(hash_consing), []).
:- hash_consing:rewritten([app(abs(_), _), app(app(*, _), _), app(_, ref(_)), abs(_), ref(_)]).
```

and [`test/hash_consing_fixtures/patterns.pl`](test/hash_consing_fixtures/patterns.pl),
which includes it:

```prolog
:- include(patterns_templates).

%   Must intern, every instance taking the first template: the shape `abs/1`
%   is written into the head.
kind(app(abs(_), _), redex).
%   Must intern, every instance taking the second template: `app/2(abs/1)`.
kind(app(app(abs(_), _), _), redex_under_an_application).
%   Must intern, every instance taking the third template: `ref/1`.
kind(app(ref(_), ref(_)), stuck).
%   Must not intern: no template matches any instance, so the head keeps the
%   plain application.
kind(app(ref(_), abs(_)), plain).
```

The Id of an interned application is `'__hash_consed_app/2'(Shape, Handle)`:
the root constructor is in the Id's name, and the shape, one atom, spells what
the term's template records below the root, `app/2(abs/1)` for the two layers
of the second template. SWI-Prolog's deep indexing then tells the first three
heads apart without looking the terms up. `app(abs(ref(0)), ref(1))` matches
the first template and the third; the first gives its shape, `abs/1`.
`app(ref(0), abs(ref(1)))` matches none, stays a plain compound, and meets the
plain head of the last clause.

A head that does not decide whether its argument is interned, such as
`size(app(Function, Argument), Size)` in the same file, gets a variable in
that position, related to the term by `hash_consing:represented/2`; the clause
keeps its meaning and loses the first argument index there. A body goal hands
such an occurrence over decided: what is bound of it must settle whether a
template matches, or the call raises an instantiation error.

## The store

The store belongs to the process: every thread and every engine interns into
it and reads its Ids, with nothing to install. An Id is never freed nor
reused, and two Ids are `==` exactly when their terms are. The size of the
store is read with `store_property/1`:

```prolog
?- hash_consing:store_property(bytes(Bytes)).
```

with the properties `ids(Count)`, `nodes(Count)` and `bytes(Bytes)`. The
Prolog flag `hash_consing_store_limit` bounds the store, as the stack and
table limits bound theirs: past it, the next insertion raises
`resource_error(hash_consing_store)` and the store keeps what it holds.

```prolog
?- set_prolog_flag(hash_consing_store_limit, 536870912).
```

A process that runs many jobs on one store, each in a thread of its own,
bounds each job by what it adds instead: `store_growth_bounded(Bytes)` lets
the calling thread grow the store by `Bytes` from the call on. Only the
thread's own insertions count, so jobs running in parallel do not charge
each other and a job is not charged with what earlier jobs interned. A
thread created later inherits the bound with a count of its own from zero,
as it inherits `stack_limit` and `table_space`. Interning a term already in
the store adds nothing and costs nothing against the budget.

```prolog
?- thread_create(( hash_consing:store_growth_bounded(268435456), job ), Thread, []).
```

An interned term is a value, not a cell: the store keeps a copy of the term
as it was when interned, and `setarg/3` or `nb_setarg/3` on the original or
on a layer read back changes that copy only. Keep mutable cells (thunks,
memory cells updated in place) out of the store. Never mutate an Id: a
handle that is not one the store gave crashes the process.

## Incompatible changes in 0.3.0

- The store is a fact of the process, no longer two global variables of the
  loading thread: a thread or engine interns into it with nothing to
  install, and code that read or set `hash_consing_store` or
  `hash_consing_spellings` drops those reads.
- In a file that opts in, the template list handed to `internalized/3` or
  `declared/1` is kept as written; 0.2.x rewrote it like any other argument.
- In a file that opts in, the first argument of `represented/2` is a plain
  layer; 0.2.x rewrote it into an Id pattern, and the call raised.
- New predicates: `store_property/1`, `store_growth_bounded/1`,
  `rewritten/2`; new Prolog flags `hash_consing_store_limit`,
  `hash_consing_growth_budget`.

## Incompatible changes in 0.2.0

- A nested template requires its constructor: `apply(apply(*, _), _)` matches
  only applications whose first argument is an application, where 0.1.0
  recorded the second layer when it was there and one layer otherwise.
- A constructor may have several templates, tried in order; `;` no longer
  writes alternatives inside a template.
- A term that no template of its constructor matches is not interned: it
  stays a plain compound, and `intern/2` fails on it.
- `intern/2` raises `existence_error(templates, Name/Arity)` on a constructor
  without templates, where 0.1.0 declared it on first use.
- A rewritten body goal raises an instantiation error when it is handed an
  occurrence whose interning is still undecided.
- `*` records the root constructor of any compound or atom, where 0.1.0 wrote
  `-` for an argument that was not an Id.
- New predicates: `declared/1`, `is_id/1` and `represented/2`.

## Test

```sh
swipl -p library=prolog --stack-limit=32m --table-space=32m -g run_tests -t halt test/hash_consing.plt
```

Run from the root of the pack, it exits with status 0 when every test passes.

## Contributing and releases

Open pull requests against `main`. `main` changes only by merging a pull
request with a merge commit, and every merge into `main` is a release:
CI runs `swipl pack publish` on the merged `main`, which tags `V<version>`
from the `version/1` of `pack.pl`, installs the pack from this repository
in an isolated directory and registers it with the SWI-Prolog pack server;
CI then makes the GitHub release of the tag, with notes GitHub generates.
A pull request into `main` must therefore raise `version/1` above every
released version; a required check enforces it.

## License

MIT. See [`LICENSE`](LICENSE).
