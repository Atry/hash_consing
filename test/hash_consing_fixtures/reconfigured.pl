%   Fixture of test/hash_consing.plt: a constructor declared
%   twice with different templates, which raises while the file loads.
:- module(reconfigured, [first/1]).
:- use_module(library(hash_consing), []).
:- hash_consing:rewritten([apply(*, _)]).
:- hash_consing:rewritten([apply(*, *)]).

first(apply(_, _)).
