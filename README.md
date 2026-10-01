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

```prolog
:- module(steps, [step/2, built/2]).
:- use_module(library(hash_consing), []).
:- hash_consing:rewritten([apply(lambda(_), _), lambda(_), variable(_)]).

step(apply(lambda(Body), Argument), beta(Body, Argument)).

built(Function, Applied) :-
    Applied = apply(Function, variable(0)).
```

Here an application is interned when its first argument is a lambda; any
other application stays a plain compound whose arguments are represented in
turn. A term that did not come through the rewrite crosses the boundary with
`hash_consing:internalized/3`, `hash_consing:externalized/2` turns Ids back
into terms, and `hash_consing:declared/1` declares templates at run time, for
constructors a program makes as it runs. The module comment of
[`prolog/hash_consing.pl`](prolog/hash_consing.pl) is the reference: the
relation `intern/2`, the Id and its shape, the templates, the rewrite of a
clause, the two rules for a file that opts in, and the known defects.

## Templates are patterns

What is interned is chosen by patterns, not by constructors. A template is
written like the clause heads it serves: a constructor applied, at each
argument position, to `_` (any argument), `*` (any argument, its root
constructor recorded) or a nested template (an argument with the nested
template's constructor, whose arguments match the nested template's). A
constructor may have several templates. They are tried in the order of the
list, the first that matches a term is its template, and a term that none
matches is not interned. From
[`test/hash_consing_fixtures/patterns.pl`](test/hash_consing_fixtures/patterns.pl):

```prolog
:- hash_consing:rewritten([app(abs(_), _), app(app(*, _), _), app(_, ref(_)), abs(_), ref(_)]).

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
in an isolated directory and registers it with the SWI-Prolog pack server.
A pull request into `main` must therefore raise `version/1` above every
released version; a required check enforces it.

## License

MIT. See [`LICENSE`](LICENSE).
