%   Fixture of test/hash_consing.plt: a module that does not opt in and
%   hands out the plain layer of an Id, as a framework's reader of one layer
%   does; `layers.pl` calls it.
:- module(layer_reader, [stored_layer/2]).
:- use_module(library(hash_consing), []).

stored_layer(Id, Layer) :-
    hash_consing:intern(Layer, Id).
