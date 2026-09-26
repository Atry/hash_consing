%   Fixture of test/hash_consing.plt: a nested template, so that
%   the shape of an application spells two layers of its first argument when
%   that argument is an application too.
:- module(spines, [head/2, inner/2]).
:- use_module(library(hash_consing), []).
:- hash_consing:rewritten([application(application(*, _), _), lambda(_), variable(_), closure(_)]).

%   Determined: two layers of the first argument are in the pattern.
head(application(application(lambda(_), _), _), redex_under_an_application).
head(application(application(closure(_), _), _), compiled_redex_under_an_application).
%   Determined: the template goes on only below an application.
head(application(lambda(_), _), redex).
%   Not determined: the inner application's own callee is unknown.
inner(application(application(Function, _), _), Function).
