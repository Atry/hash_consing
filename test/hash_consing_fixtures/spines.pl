%   Fixture of test/hash_consing_rewrite.pl: a nested template, so that
%   the shape of an application spells two layers of its first argument when
%   that argument is an application too.
:- module(spines, [head/2, inner/2]).
:- use_module('../../prolog/hash_consing', []).
:- hash_consing:rewritten([apply(apply(*, _), _), lambda(_), variable(_), closure_a(_)]).

%   Determined: two layers of the first argument are in the pattern.
head(apply(apply(lambda(_), _), _), redex_under_an_application).
head(apply(apply(closure_a(_), _), _), compiled_redex_under_an_application).
%   Determined: the template goes on only below an application.
head(apply(lambda(_), _), redex).
%   Not determined: the inner application's own callee is unknown.
inner(apply(apply(Function, _), _), Function).
