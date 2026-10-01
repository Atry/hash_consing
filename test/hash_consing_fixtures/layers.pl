%   Fixture of test/hash_consing.plt: layer positions. The first argument of
%   represented/2, and the positions `layer_arguments` names, keep the
%   constructor written there as a plain layer; its arguments are rewritten
%   as anywhere else.
:- module(layers, [slot_made/2, slot_index/2, slot_read/2, linked_index/2, marked_name/2,
                   is_slot/1]).
:- use_module(library(hash_consing), []).
:- use_module(layer_reader, [stored_layer/2]).
:- hash_consing:rewritten([slot(_), link(_, _), marked(_)],
                          [layer_arguments([stored_layer(_, layer), marked_name(layer, _)])]).

%   The layer `slot(Index)` represented, and read back from an Id.
slot_made(Index, Slot) :-
    hash_consing:represented(slot(Index), Slot).
slot_index(Slot, Index) :-
    hash_consing:represented(slot(Index), Slot).

%   The plain layer a module that does not opt in hands out, matched as
%   written.
slot_read(Slot, Index) :-
    stored_layer(Slot, slot(Index)).

%   A listed constructor inside a layer is an Id, as anywhere else.
linked_index(Link, Index) :-
    stored_layer(Link, link(slot(Index), _)).

%   A head whose first argument is a layer.
marked_name(marked(Name), Name).

%   An unread occurrence: its argument occurs nowhere else, so the goal
%   matches the Id pattern and reads nothing back.
is_slot(Value) :-
    Value = slot(_).
