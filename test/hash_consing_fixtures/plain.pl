%   Fixture of test/hash_consing_rewrite.pl: no constructor has a shape,
%   so every Id records its root constructor only.
:- module(plain, [doubled/2, swapped/2]).
:- use_module('../../prolog/hash_consing', []).
:- hash_consing:rewritten([pair(_, _)]).

doubled(X, pair(X, X)).

swapped(pair(A, B), pair(B, A)).
