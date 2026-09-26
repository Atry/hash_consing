%   Fixture of test/hash_consing.plt: clauses told apart by an
%   inner constructor; the template apply(*, _) records the root constructor
%   of an application's first argument.
:- module(steps, [step/2, callee/2, built/2, constant/1]).
:- use_module(library(hash_consing), []).
:- hash_consing:rewritten([apply(*, _), lambda(_), variable(_), closure_a(_), closure_b]).

%   The shape is determined: the atom goes into the head.
step(apply(lambda(Body), Argument), beta(Body, Argument)).
step(apply(closure_a(Capture), Argument), compiled(Capture, Argument)).
step(apply(closure_b, Argument), constant(Argument)).
step(apply(apply(Function, First), Second), spine(Function, First, Second)).

%   The shape is not determined: the head keeps an unbound shape.
callee(apply(Function, _), Function).

%   A body goal that builds a shaped term.
built(Function, Applied) :-
    Applied = apply(Function, variable(0)).

%   A ground occurrence is interned while the file loads.
constant(apply(lambda(variable(0)), closure_b)).
