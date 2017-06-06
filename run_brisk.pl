:- use_module('rewrite.pl').

user:runtime_entry(start) :-
	prolog_flag(argv, Argv),
	format('% ~p\n', [Argv]), 
	(   Argv = [T|_] ->
	    format('Rewriting term:~p~n',[T]),
%	    check_race_freedom(T, T1),
	    rewrite(T, skip, [], _, Delta, _),
	    format('~p',[Delta])
	).