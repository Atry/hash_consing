%   Fixture of test/hash_consing.plt: the templates of `patterns.pl`, kept in a
%   file of their own that every file handing these terms to another includes.
:- use_module(library(hash_consing), []).
:- hash_consing:rewritten([app(abs(_), _), app(app(*, _), _), app(_, ref(_)), abs(_), ref(_)]).
