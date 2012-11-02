/* Grammatica

se C e' una categoria sintattica allora C* e' una sequenza finita (eventualmente vuota) di
espressioni di categoria C (realizzata con una lista)

Var ::= a| b | c | x | y | z | Var i   (i in Nat)

Num ::= 0 | 1 | ...

Bool ::= true | false

Exp ::= Var | Num | Bool | Exp + Exp | Exp and Exp

Proc ::= stop | input(Var, Var*, Proc) | rec(Var, Var*, Proc)
      |  output(Var, Exp*, Proc) | par(Proc, Proc) | nu(Var, Proc)
      |  ite(Exp, Proc, Proc)

Type ::= int | bool | chan(Type*)    

Typing ::= hasType(Var, Type)

Env ::= Typing*

*/

% Operatori

:- op(110, xfx, and).
:- op(110, xfx, or).
:- op(110, xfx, neq).

% Utilita'

member(X, [X]).
member(X, [X|_]).
member(X, [_|Y]) :- member(X,Y).

% Predicati relativi alle cat. sintattiche

is_Var(X) :-
	atom(X).

% Predicati relativi agli ambienti

% una variabile e' tipata se e' tipata nell'ambiente
inDom(Var, [hasType(Var,_)|_]).

inDom(Var, [_|Delta]) :- inDom(Var, Delta).

% controlla che la variabile V abbia tipo T nell'ambiente oppure che non sia presente in quell'ambiente
typeInEnv(Var, T, [hasType(Var,T)|_]) :- !.

typeInEnv(Var, T, [hasType(Var, T2)|_]) :- T\=T2, !, fail.

typeInEnv(Var, T, [_|Delta]) :- typeInEnv(Var, T, Delta).

typeInEnv(_, _, []).

% unisce due ambienti in modo che il risultato sia ancora un ambiente
merge_Env([hasType(Var, T)|_], Delta2, _) :-
	not(member(hasType(Var, T), Delta2)),
	inDom(Var, Delta2), !, fail.

merge_Env([], Delta, Delta) :- !.

merge_Env([hasType(Var,T)|Delta1], Delta2, Delta3) :-
	member(hasType(Var,T), Delta2), !,
	merge_Env(Delta1, Delta2, Delta3), !.

merge_Env([hasType(Var,T)|Delta1], Delta2, [hasType(Var,T)|Delta3]) :-
	merge_Env(Delta1, Delta2, Delta3), !.

% hasType applicato su una lista (per input poliadico)
hasType_L([], []).

hasType_L([H|T], [hasType(H,_)|HTT]) :-
	hasType_L(T, HTT).

% cancella tutti gli elementi della seconda lista dalla prima
delete_L(L1, [], L1).

delete_L(L1, [H|T], LL) :-
	delete(L1, H, TL),
	delete_L(TL, T, LL).

% estrae una lista di tipi da una lista di hasType
type_List([], []).

type_List([hasType(_, T)|Tail], [T|TypeTail]) :-
	type_List(Tail, TypeTail).

% unisce all'ambiente Delta la lista di hasType
merge_List(Delta, [], Delta).

merge_List(DeltaI, [H|T], DF) :-
	merge_Env(H, DeltaI, DeltaT),
	merge_List(DeltaT, T, DF).

% deriva i tipi degli elementi di una lista in una lista di ambienti
der_List([], _, []).

der_List([H|T], [DeltaI|DeltaT], [Ty|TT]) :-
	der(DeltaI, H, Ty),
	der_List(T, DeltaT, TT).

% controlla che il canale non occorra nei suoi argomenti
check(_, []).

check(hasType(Chan, chan(_)), [hasType(Chan, _) | _]) :- !, fail.

check(hasType(Chan, chan(T)), [ _ | TT]) :-
	check(hasType(Chan, chan(T)), TT).

% Assegnamento per le espressioni
der(_, true, bool).

der(_, false, bool).

der(_, stop, proc).

% Polyadic
der(Delta, input(Chan, Input, P), proc) :-
	der(Delta1, P, proc),
	hasType_L(Input, InputHT),
	type_List(InputHT, InputT),
	merge_Env([hasType(Chan, chan(InputT)) | InputHT], Delta1, Delta2), !,
	delete_L(Delta2, InputHT, Delta).

der(Delta, rec(Chan, Input, P), proc) :-
	der(Delta1, P, proc),
	hasType_L(Input, InputHT),
	type_List(InputHT, InputT),
	merge_Env([hasType(Chan, chan(InputT)) | InputHT], Delta1, Delta2), !,
	delete_L(Delta2, InputHT, Delta).

der(Delta, output(Chan, Output, P), proc) :-
	der(Delta1, P, proc),
	der_List(Output, [HDelta2L|TDelta2L], T),
	merge_List(HDelta2L, TDelta2L, RDelta2),
	reverse(RDelta2, Delta2),
	merge_Env([hasType(Chan, chan(T))], Delta1, Delta3),
	check(hasType(Chan, chan(T)), Delta2),
	merge_Env(Delta3, Delta2, Delta), !.

% Monadic 
der(Delta, input(Chan, Input, P), proc) :-
	der(Delta1, P, proc),
	merge_Env([hasType(Chan, chan([T])), hasType(Input, T)], Delta1, Delta2), !,
	delete(Delta2, hasType(Input, _), Delta).

der(Delta, rec(Chan, Input, P), proc) :-
	der(Delta1, P, proc),
	merge_Env([hasType(Chan, chan([T])), hasType(Input, T)], Delta1, Delta2), !,
	delete(Delta2, hasType(Input, _), Delta).

der(Delta, output(Chan, Output, P), proc) :-
	der(Delta1, P, proc),
	der(Delta2, Output, T),
	merge_Env([hasType(Chan, chan([T]))], Delta1, Delta3),
	check(hasType(Chan, chan(T)), Delta2),
	merge_Env(Delta3, Delta2, Delta), !.

% Shared
der(Delta, par(P, Q), proc) :-
	der(Delta1, P, proc),
	der(Delta2, Q, proc),
	merge_Env(Delta1, Delta2, Delta), !.

der(Delta, nu(Chan, P), proc) :-
	der(Delta1, P, proc),
	typeInEnv(Chan,chan(_),Delta1),
	delete(Delta1, hasType(Chan,chan([_])), Delta).

der(Delta, ite(Exp, Proc1, Proc2), proc) :-
	der(Delta1, Exp, bool),
	der(Delta2, Proc1, proc),
	der(Delta3, Proc2, proc),
	merge_Env(Delta1, Delta2, DeltaT),
	merge_Env(Delta3, DeltaT, Delta), !.

der(_, Num, int) :- integer(Num).

der([hasType(Var,T)], Var, T) :-
	is_Var(Var).

der(Delta, Exp, T) :-
	Exp =.. E,
	der_E(Delta, E, T).

der_E(Delta, [F, Exp1, Exp2], int) :-
	member(F, ['+', '*', '-', '/']), !,
	der_E_M(Exp1, Exp2, int, Delta).

der_E(Delta, [F, Exp1, Exp2], bool) :-
	member(F, ['and', 'or']), !,
	der_E_M(Exp1, Exp2, bool, Delta).

der_E(Delta, [F, Exp1, Exp2], bool) :-
	member(F, ['=', 'neq', '>', '<']), !,
	der_E_M(Exp1, Exp2, _, Delta).

der_E_M(Exp1, Exp2, T, Delta) :-
	der(Delta1, Exp1, T),
	der(Delta2, Exp2, T),
	merge_Env(Delta1, Delta2, Delta).

write_Env([]).

write_Env([hasType(V, Ty) | T]) :-
	format('~a : ', [V]),
	print_Env(Ty),
	format('~n'),
	write_Env(T).

print_Env(T) :-
	(atom(T) ; gensym(t, Ty), T = Ty), !,
	format('~a', [T]).

print_Env(chan(T)) :-
	format('chan('),
	print_Type_List(T),
	format(')').

print_Type_List([]).

print_Type_List([L]) :-
	print_Env(L), !.

print_Type_List([H | T]) :-
	print_Env(H),
	format(', '),
	print_Type_List(T).

type(Term) :-
	reset_gensym,
	der(D, Term, proc),
	write_Env(D).
