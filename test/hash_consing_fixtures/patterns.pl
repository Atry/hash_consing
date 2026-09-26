%   Fixture of test/hash_consing.plt: templates as patterns. The constructor
%   `app/2` has three templates, tried in order, and an application that none
%   of them matches stays a plain compound; the occurrences below fall in the
%   three classes of the rewrite.
:- module(patterns, [kind/2, size/2, wrapped/2, first/2, built/2, unbound_built/1]).
:- use_module(library(hash_consing), []).
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

%   Undetermined at the top of a head: a fresh variable there, related to the
%   layer by represented/2.
size(app(Function, Argument), Size) :-
    size(Function, FunctionSize),
    size(Argument, ArgumentSize),
    Size is FunctionSize + ArgumentSize + 1.
size(abs(Body), Size) :-
    size(Body, BodySize),
    Size is BodySize + 1.
size(ref(_), 1).

%   Undetermined in an output position of a head.
wrapped(Function, app(Function, abs(ref(0)))).

%   Undetermined, with a cut after the body has bound it: the answer is the
%   one of the program without interning, whichever representation it gets.
first(Pairs, app(Function, Argument)) :-
    member(Function-Argument, Pairs),
    !.

%   Undetermined in a body goal, decided when the goal is called.
built(Function, Built) :-
    Built = app(Function, abs(ref(0))).

%   Undetermined in a body goal and still undecided when it is called.
unbound_built(Built) :-
    Built = app(_, abs(ref(0))).
