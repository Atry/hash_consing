# hash_consing

[![CI](https://github.com/Atry/hash_consing/actions/workflows/ci.yml/badge.svg)](https://github.com/Atry/hash_consing/actions/workflows/ci.yml)

Hash-consed terms for SWI-Prolog, and a load-time rewrite that makes a
program use them. A file is written as the program that does not intern and
names the constructors to intern; every clause read after that directive
refers to their instances by Ids, each wrapping a node handle of one trie,
and the store is canonical: the same term has the same Id.

## Install

```prolog
?- pack_install(hash_consing).
```

## Use

```prolog
:- module(steps, [step/2, built/2]).
:- use_module(library(hash_consing), []).
:- hash_consing:rewritten([apply(*, _), lambda(_), variable(_)]).

step(apply(lambda(Body), Argument), beta(Body, Argument)).

built(Function, Applied) :-
    Applied = apply(Function, variable(0)).
```

A term that did not come through the rewrite crosses the boundary with
`hash_consing:internalized/3`, and `hash_consing:externalized/2` turns Ids back
into terms. The module comment of [`prolog/hash_consing.pl`](prolog/hash_consing.pl)
is the reference: the relation `intern/2`, the Id and its shape, the
templates, the rewrite of a clause, the two rules for a file that opts in,
and the known defects.

## Test

```sh
test/hash_consing_rewrite.sh | diff - test/hash_consing_rewrite_baseline.txt
```

prints nothing when the rewrite and `intern/2` behave as specified.

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
