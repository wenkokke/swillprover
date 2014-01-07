%
%  Linear Logic Prover for SICStus Prolog
%  by Naoyuki Tamura (tamura@kobe-u.ac.jp)
%     Dept. Computer & Systems Eng., Kobe Univ., Japan
%  TeX form output by Eiji Sugiyama (eiji@grad306c.scitec.kobe-u.ac.jp)
%
%  You can freely distribute or modify this program.
%
%  Version 1.0
%   2/ 9/1995 version 1.0 released
%   2/14/1995 redundant parentheses of tex output for all(X,a(X))
%             are removed
%   2/14/1995 tex output is modified to use \drv
%   2/14/1995 bug fix to allow l(!) on c(!) and r(?) on c(?)
%   2/15/1995 output(-N) command is added
%   2/15/1995 style(onesided) command is added
%   2/15/1995 position of principal branch is added to a proof
%   2/15/1995 tex output is modified to use \lnot{#1}, \LR, \RR,
%             \WR, \CR, \DR
%   2/16/1995 style(proofnet) command is added
%   2/16/1995 bug fix not to close log after ll_prover
%   2/16/1995 form command is renamed to output command
%   2/16/1995 nesting of consult is allowed
%   2/21/1995 <--> is added
%  Version 1.1 beta
%   2/21/1995 version 1.1 beta released
%   3/ 7/1995 bug fix for eigen variable condition
%   3/ 9/1995 deterministic choice of invertible rules
%   3/ 9/1995 bug fix, assert(proved(P,M,N))
%  Version 1.1
%   3/ 9/1995 version 1.1 released
%   2/17/1997 flush_output is renamed
%  Version 1.2
%   2/17/1997 version 1.2 released
%   5/ 8/1997 bug fix for quantifier rules
%   5/ 8/1997 variables are named in pretty print
%  Version 1.3
%   5/ 8/1997 version 1.3 released
%  12/19/1997 bug fix for proved/3 and not_proved/2
%
:- expects_dialect(sicstus).

:- dynamic
	ll_system/2, threshold/1, style/1, output_form/1, logging/2,
	output_count/1, output_result/2,
	proved/3, not_proved/2, axiom/1.

:- op(1200, xfy, & ).
:- op(1190, xfx, [ -->, <--> ]).
:- op(1000, fx, @ ).
:- op( 910, xfy, -> ).
:- op( 500, xfy, [ +, /\, \/ ]).
:- op( 400, xfy, * ).
:- op( 300, fy,  [ ~, !, ? ]).

ll :-
	writex('Linear Logic Prover ver 1.3 for SICStus Prolog'), nlx,
	writex('        http://bach.seg.kobe-u.ac.jp/llprover/'), nlx,
	writex('        by Naoyuki Tamura (tamura@kobe-u.ac.jp)'), nlx,
	ll_init,
	statistics(runtime, [T0,_]),
	ll_prover,
	statistics(runtime, [T1,_]),
	T is T1-T0,
	writex('Exit from Linear Logic Prover...'), nlx,
	writex('Total CPU time = '), writex(T), writex(' msec.'), nlx,
	log_end.

ll_init :-
	set_system(ill,0),
	set_threshold(5),
	set_axioms([]),
	set_style(twosided),
	set_output_form(pretty),
	log_end,
	reset_output_result.

ll_prover :-
	current_input(STR),
	ll_prover(STR).

ll_prover(STR) :-
	repeat,
	  ll_system(Sys, Opt),
	  writex(Sys), writex('('), writex(Opt), writex(')'),
	  writex('> '),
	  readx(STR, X),
	  ll_command(X),
	ll_quit(X),
	close(STR).

ll_quit(X) :-
	nonvar(X),
	memberq(X, [quit, end, bye, halt, end_of_file]).

ll_command(X) :-
	ll_execute(X),
	!,
	writex(yes), nlx.
ll_command(_) :-
	writex(no), nlx.

ll_execute(X) :- var(X), !, fail.
ll_execute(X) :- ll_quit(X), !.
ll_execute((X & Y)) :- !, ll_execute(X), ll_execute(Y).
ll_execute(help) :- !, ll_help.
ll_execute(init) :- !, ll_init.
ll_execute([File]) :- !, ll_consult(File).
ll_execute(cll(Opt)) :- !, set_system(cll,Opt).
ll_execute(ilz(Opt)) :- !, set_system(ilz,Opt).
ll_execute(ill(Opt)) :- !, set_system(ill,Opt).
ll_execute(threshold(N)) :- var(N), !,
	threshold(N),
	writex(threshold(N)), nlx.
ll_execute(threshold(N)) :- !,
	set_threshold(N).
ll_execute(axioms(As)) :- var(As), !,
	(bagof(A, axiom(([]-->[A])), As); As=[]), !,
	writex(axioms(As)), nlx.
ll_execute(axioms(As)) :- !,
	set_axioms(As).
ll_execute(style(Style)) :- var(Style), !,
	style(Style),
	writex(style(Style)), nlx.
ll_execute(style(Style)) :-
	set_style(Style).
ll_execute(output(Form)) :- var(Form), !,
	output_form(Form),
	writex(output(Form)), nlx.
ll_execute(output(Form)) :-
	set_output_form(Form).
ll_execute(log(File)) :- var(File), !,
	logging(File, _),
	writex(log(File)), nlx.
ll_execute(log(no)) :- !,
	log_end.
ll_execute(log(File)) :- !,
	log_start(File).
ll_execute(N) :- integer(N), !,
	get_output_result(N, N1, P),
	print_output(N1, P).
ll_execute((@Goal)) :- !,
	call(Goal).
ll_execute((Xs <--> Ys)) :- !,
	ll_execute(((Xs --> Ys) & (Ys --> Xs))).
ll_execute((Xs --> Ys)) :-
	convert_to_seq((Xs --> Ys), Seq),
	sequentq(Seq),
	!,
	ll_prove(Seq).
ll_execute(X) :-
	writex('Error '),
	writex(X),
	writex(' is not a command nor a sequent.'), nlx.

ll_help :-
	writex('A1,...,Am -->  B1,...,Bn : Try to prove the sequent.'), nlx,
	writex('A1,...,Am <--> B1,...,Bn : Try to prove the sequent '),
	    writex('in both directions.'), nlx,
	writex('com1 & com2    : Multiple commands.'), nlx,
	writex('help           : Help.'), nlx,
	writex('init           : Initialize the prover.'), nlx,
	writex('[File]         : Read from the file.'), nlx,
	writex('Sys(Opt)       : Select the system. '),
	    writex('Sys={cll|ilz|ill}, Opt={full|e|q|0}'), nlx,
	writex('threshold(N)   : Set/retrieve the threshold. N>=0'), nlx,
	writex('axioms(Axioms) : Set/retrieve the axioms. '),
	    writex('Axioms=[A1,...,Am]'), nlx,
	writex('style(Style)   : Set/retrieve the output style. '),
	    writex('Style={twosided|onesided}'), nlx,
	writex('output(Form)   : Set/retrieve the output form. '),
	    writex('Form={pretty|tex|standard|term}'), nlx,
	writex('log(L)         : Start/stop/retrieve the output logging. '),
	    writex('L={yes|File|no}'), nlx,
	writex('N              : Display the N-th output.'), nlx,
	writex('@Goal          : Call Prolog.'), nlx,
	writex('quit           : Quit.'), nlx.

ll_consult(File) :-
	open(File, read, STR),
	ll_prover(STR).

ll_prove(Seq) :-
	statistics(runtime,[_,_]),
	prove(Seq, Proof),
	statistics(runtime,[_,Time]),
	writex('Succeed in proving '),
	write_seq(Seq),
	writex(' ('), writex(Time), writex(' msec.)'), nlx,
	output_count(N),
	assert_output_result(Proof),
	!,
	print_output(N, Proof).
ll_prove(Seq) :-
	statistics(runtime,[_,Time]),
	writex('Fail to prove '),
	write_seq(Seq),
	writex(' ('), writex(Time), writex(' msec.)'), nlx.

print_output(N, P) :-
	style(Style), writex(Style), writex(':'),
	output_form(Form), writex(Form), writex(':'),
	writex(N), writex(' ='), nlx,
	print_proof(P).

print_proof(P) :-
	style(S),
	print_proof(S, P).

print_proof(S, P) :-
	convert_proof(S, P, Q),
	!,
	output_form(Form),
	print_proof_form(Form, Q).
print_proof(S, _) :-
	writex('Fail to convert to '),
	writex(S), writex(' style.'), nlx.

convert_proof(twosided, P, twosided(P)).
convert_proof(onesided, P, onesided(Q)) :-
	convert_to_onesided(P, Q).
convert_proof(proofnet, P, proofnet(Q)) :-
	convert_to_proofnet(P, Q).

print_proof_form(pretty, P) :- !,
	pretty_print(P).
print_proof_form(tex, P) :- !,
	tex_print(P).
print_proof_form(standard, P) :- !,
	standard_print(P).
print_proof_form(term, P) :- !,
	writex(P), nlx.

set_system(Sys, Opt) :-
	memberq(Sys, [ill,ilz,cll]),
	memberq(Opt, [0,q,e,full]),
	retractall(ll_system(_,_)),
	assert(ll_system(Sys,Opt)).

set_threshold(N) :-
	integer(N), N >= 0,
	retractall(threshold(_)),
	assert(threshold(N)).

set_axioms(Axioms) :-
	retractall(axiom(_)),
	assert_axioms(Axioms).

assert_axioms([]).
assert_axioms([A|As]) :-
	formulaq(A),
	!,
	assert(axiom(([]-->[A]))),
	assert_axioms(As).
assert_axioms([A|As]) :-
	writex('Error '), writex(A),
	writex(' is not a formula.'), nlx,
	assert_axioms(As).

set_style(Style) :-
	memberq(Style, [twosided, onesided, proofnet]),
	retractall(style(_)),
	assert(style(Style)).

set_output_form(Form) :-
	memberq(Form, [pretty, tex, standard, term]),
	retractall(output_form(_)),
	assert(output_form(Form)).

reset_output_result :-
	retractall(output_count(_)),
	retractall(output_result(_,_)),
	assert(output_count(1)).

assert_output_result(P) :-
	output_count(N),
	assert(output_result(N,P)),
	retractall(output_count(_)),
	N1 is N+1,
	assert(output_count(N1)).

get_output_result(N, N, P) :- N>0, !,
	output_result(N, P).
get_output_result(N, N1, P) :-
	output_count(M),
	N1 is M+N,
	output_result(N1, P).

convert_to_seq((Xs --> Ys), (Xs1 --> Ys1)) :-
	convert_to_list(Xs, Xs1), convert_to_list(Ys, Ys1).

convert_to_list(X, _) :- var(X), !, fail.
convert_to_list([], []) :- !.
convert_to_list([X|Xs], [X|Xs]) :- !.
convert_to_list((X,Xs), [X|Zs]) :- !, convert_to_list(Xs, Zs).
convert_to_list(X, [X]).

sequentq((X-->Y)) :- formula_listq(X), formula_listq(Y).

formula_listq([]).
formula_listq([A|As]) :- formulaq(A), formula_listq(As).

formulaq(A) :- var(A), !, fail.
formulaq((_-->_)) :- !, fail.
formulaq([]) :- !, fail.
formulaq([_|_]) :- !, fail.
formulaq(~A) :- !, formulaq(A).
formulaq(A*B) :- !, formulaq(A), formulaq(B).
formulaq(A/\B) :- !, formulaq(A), formulaq(B).
formulaq(A+B) :- !, formulaq(A), formulaq(B).
formulaq(A\/B) :- !, formulaq(A), formulaq(B).
formulaq(A->B) :- !, formulaq(A), formulaq(B).
formulaq(all(_X,A)) :- !, formulaq(A).
formulaq(exists(_X,A)) :- !, formulaq(A).
formulaq(!A) :- !, formulaq(A).
formulaq(?A) :- !, formulaq(A).
formulaq(_).

%
%  Linear Logic Prover
%
%  ll_system( {ill|ilz|cll}, {0|q|e|full} ).
%    ll_system(cll,full).
%  Max number of cut and contraction rules: cut, c(!), c(?)
%    threshold(5).
%  Axioms
%    axiom(Ax1). axiom(Ax2). ....

prove(S, P) :-
	retractall(proved(_,_,_)),
	retractall(not_proved(_,_)),
	threshold(N),
	writex('Trying to prove with threshold ='),
	for(I, 0, N),
	writex(' '), writex(I),
	flush_out,
	prove(S, P, I),
	nlx,
	!.
prove(_S, _P) :-
	nlx,
	fail.

prove(S, _P, N) :-
	ground(S),
	clause(not_proved(S,M), _),
	N =< M,
	!,
	fail.
prove(S, P, N) :-
	ground(S),
	clause(proved(S,P,M), _),
	M =< N,
	!.
prove(S, P, _N) :-
	clause(axiom(S), _),
	P = [axiom,[[]],S],
	!.
prove(S, P, N) :-
	check_sequent(S),
	select_rule(Rule, S, Ss, Pos),
	P = [Rule,Pos,S|Ps],
	set_sequents(Ss, Ps),
	rule_constraint(Rule, Ps, M),
	N1 is N-M, N1 >= 0,
       	prove_all(Ss, Ps, N1),
	!,
	assert(proved(S,P,N)).
prove(S, _P, N) :-
	ground(S),
	assert(not_proved(S,N)),
%	write(not_proved(S,N)), nl,
	!,
	fail.

prove_all([], [], _N).
prove_all([S|Ss], [P|Ps], N) :-
	prove(S, P, N),
	prove_all(Ss, Ps, N).

check_sequent(_) :- ll_system(cll,_), !.
check_sequent((_X-->Y)) :- (Y=[]; Y=[_]), !.

select_rule(Rule, S, Ss, Pos) :-
	rule(RuleSys, inv, Rule, S, Ss, Pos),
	check_rule(RuleSys),
	!.
select_rule(Rule, S, Ss, Pos) :-
	rule(RuleSys, no, Rule, S, Ss, Pos),
	check_rule(RuleSys).

check_rule([RSys,ROp]) :-
	ll_system(Sys,Op),
	check_rule1(Sys, RSys),
	check_rule2(Op, ROp),
	!.

check_rule1(Sys, Sys).
check_rule1(ilz, ill).
check_rule1(cll, _).

check_rule2(Op, Op).
check_rule2(q, 0).
check_rule2(e, 0).
check_rule2(full, _).

set_sequents([], []).
set_sequents([S|Ss], [[_,_,S|_]|Ps]) :- set_sequents(Ss, Ps).

rule_constraint(cut, [P1,_P2], 1) :- !,
	axiom(S1),
	P1 = [axiom,_,S1].
rule_constraint(c(!), [P1], 1) :- !,
	P1 = [NextRule,_,_|_],
	freeze(NextRule, memberq(NextRule, [r(*),l(+),l(->),c(!),c(?),l(!)])).
%	freeze(NextRule, memberq(NextRule, [r(*),l(+),l(->),c(!),c(?)])).
rule_constraint(c(?), [P1], 1) :- !,
	P1 = [NextRule,_,_|_],
	freeze(NextRule, memberq(NextRule, [r(*),l(+),l(->),c(!),c(?),r(?)])).
%	freeze(NextRule, memberq(NextRule, [r(*),l(+),l(->),c(!)])).
rule_constraint(_Rule, _, 0).

% Logical axiom
rule([ill,0], inv, ax, S, [], [[]]) :-
	match(S,  ([[A]]-->[[A]])).
% Rules for the propositional constants
rule([ill,0], inv, l(1), S, [S1], [l(N),[]]) :-
	match(S,  ([X1,[1],X2]-->[Y])),
	match(S1, ([X1,X2]-->[Y])),
	length(X1, N).
rule([ill,0], inv, r(1), S, [], [r(0)]) :-
	match(S,  ([[]]-->[[1]])).
rule([ill,0], inv, r(top), S, [], [r(N)]) :-
	match(S,  ([_X]-->[Y1,[top],_Y2])),
	length(Y1, N).
rule([ilz,0], inv, r(0), S, [S1], [r(N),[]]) :-
	match(S,  ([X]-->[Y1,[0],Y2])),
	match(S1, ([X]-->[Y1,Y2])),
	length(Y1, N).
rule([ilz,0], inv, l(0), S, [], [l(0)]) :-
	match(S,  ([[0]]-->[[]])).
rule([ill,0], inv, l(bot), S, [], [l(N)]) :-
	match(S,  ([X1,[bot],_X2]-->[_Y])),
	length(X1, N).
% Rules for the propositional connectives
rule([ilz,0], inv, l(~), S, [S1], [l(N),r(0)]) :-
	match(S,  ([X1,[~A],X2]-->[Y])),
	match(S1, ([X1,X2]-->[[A],Y])),
	length(X1, N).
rule([ilz,0], inv, r(~), S, [S1], [r(N),l(0)]) :-
	match(S,  ([X]-->[Y1,[~A],Y2])),
	match(S1, ([[A],X]-->[Y1,Y2])),
	length(Y1, N).
rule([ill,0], no,  l(/\,1), S, [S1], [l(N),l(N)]) :-
	match(S,  ([X1,[A/\_B],X2]-->[Y])),
	match(S1, ([X1,[A],X2]-->[Y])),
	length(X1, N).
rule([ill,0], no,  l(/\,2), S, [S1], [l(N),l(N)]) :-
	match(S,  ([X1,[_A/\B],X2]-->[Y])),
	match(S1, ([X1,[B],X2]-->[Y])),
	length(X1, N).
rule([ill,0], inv, r(/\), S, [S1, S2], [r(N),r(N),r(N)]) :-
	match(S,  ([X]-->[Y1,[A/\B],Y2])),
	match(S1, ([X]-->[Y1,[A],Y2])),
	match(S2, ([X]-->[Y1,[B],Y2])),
	length(Y1, N).
rule([ill,0], inv, l(*), S, [S1], [l(N),[l(N),l(N1)]]) :-
	match(S,  ([X1,[A*B],X2]-->[Y])),
	match(S1, ([X1,[A,B],X2]-->[Y])),
	length(X1, N), N1 is N+1.
rule([ill,0], no,  r(*), S, [S1, S2], [r(N),r(N1),r(N2)]) :-
	match(S,  ([X]-->[Y1,[A*B],Y2])),
	merge(X1, X2, X),
	merge(Y11, Y12, Y1),
	merge(Y21, Y22, Y2),
	match(S1, ([X1]-->[Y11,[A],Y21])),
	match(S2, ([X2]-->[Y12,[B],Y22])),
	length(Y1, N), length(Y11, N1), length(Y12, N2).
rule([ill,0], inv, l(\/), S, [S1, S2], [l(N),l(N),l(N)]) :-
	match(S,  ([X1,[A\/B],X2]-->[Y])),
	match(S1, ([X1,[A],X2]-->[Y])),
	match(S2, ([X1,[B],X2]-->[Y])),
	length(X1, N).
rule([ill,0], no,  r(\/,1), S, [S1], [r(N),r(N)]) :-
	match(S,  ([X]-->[Y1,[A\/_B],Y2])),
	match(S1, ([X]-->[Y1,[A],Y2])),
	length(Y1, N).
rule([ill,0], no,  r(\/,2), S, [S1], [r(N),r(N)]) :-
	match(S,  ([X]-->[Y1,[_A\/B],Y2])),
	match(S1, ([X]-->[Y1,[B],Y2])),
	length(Y1, N).
rule([cll,0], no,  l(+), S, [S1, S2], [l(N),l(N1),l(N2)]) :-
	match(S,  ([X1,[A+B],X2]-->[Y])),
	merge(X11, X12, X1),
	merge(X21, X22, X2),
	merge(Y1, Y2, Y),
	match(S1, ([X11,[A],X21]-->[Y1])),
	match(S2, ([X12,[B],X22]-->[Y2])),
	length(X1, N), length(X11, N1), length(X12, N2).
rule([cll,0], inv, r(+), S, [S1], [r(N),[r(N),r(N1)]]) :-
	match(S,  ([X]-->[Y1,[A+B],Y2])),
	match(S1, ([X]-->[Y1,[A,B],Y2])),
	length(Y1, N), N1 is N+1.
rule([ill,0], no,  l(->), S, [S1, S2], [l(N),r(0),l(N2)]) :-
	match(S,  ([X1,[A->B],X2]-->[Y])),
	merge(X11, X12, X1),
	merge(X21, X22, X2),
	merge(Y1, Y2, Y),
	match(S1, ([X11,X21]-->[[A],Y1])),
	match(S2, ([X12,[B],X22]-->[Y2])),
	length(X1, N), length(X12, N2).
rule([ill,0], inv, r(->), S, [S1], [r(N),[l(0),r(N)]]) :-
	match(S,  ([X]-->[Y1,[A->B],Y2])),
	match(S1, ([[A],X]-->[Y1,[B],Y2])),
	length(Y1, N).
% Rules for the quantifiers
rule([ill,q], no,  l(all), S, [S1], [l(N),l(N)]) :-
	match(S,  ([X1,[all(V,A)],X2]-->[Y])),
%	copy_term(all(V,A), all(_V1,A1)),
	substitute(V, _V1, A, A1),
	match(S1, ([X1,[A1],X2]-->[Y])),
	length(X1, N).
rule([ill,q], inv, r(all), S, [S1], [r(N),r(N)]) :-
	match(S,  ([X]-->[Y1,[all(V,A)],Y2])),
%	copy_term(all(V,A), all(V1,A1)),
	substitute(V, V1, A, A1),
	match(S1, ([X]-->[Y1,[A1],Y2])),
	eigen_variable(V1, S),
	length(Y1, N).
rule([ill,q], inv, l(exists), S, [S1], [l(N),l(N)]) :-
	match(S,  ([X1,[exists(V,A)],X2]-->[Y])),
%	copy_term(exists(V,A), exists(V1,A1)),
	substitute(V, V1, A, A1),
	match(S1, ([X1,[A1],X2]-->[Y])),
	eigen_variable(V1, S),
	length(X1, N).
rule([ill,q], no,  r(exists), S, [S1], [r(N),r(N)]) :-
	match(S,  ([X]-->[Y1,[exists(V,A)],Y2])),
%	copy_term(exists(V,A), exists(_V1,A1)),
	substitute(V, _V1, A, A1),
	match(S1, ([X]-->[Y1,[A1],Y2])),
	length(Y1, N).
% Rules for the exponentials
rule([ill,e], no,  w(!), S, [S1], [l(N),[]]) :-
	match(S,  ([X1,[!_A],X2]-->[Y])),
	match(S1, ([X1,X2]-->[Y])),
	length(X1, N).
rule([ill,e], no,  l(!), S, [S1], [l(N),l(N)]) :-
	match(S,  ([X1,[!A],X2]-->[Y])),
	match(S1, ([X1,[A],X2]-->[Y])),
	length(X1, N).
rule([ill,e], inv, r(!), S, [S1], [r(N),r(N)]) :-
	match(S,  ([X]-->[Y1,[!A],Y2])),
	all_ofcourse(X),
	all_whynot(Y1), all_whynot(Y2),
	match(S1, ([X]-->[Y1,[A],Y2])),
	length(Y1, N).
rule([ill,e], no,  c(!), S, [S1], [l(N),[l(N),l(N1)]]) :-
	match(S,  ([X1,[!A],X2]-->[Y])),
	match(S1, ([X1,[!A,!A],X2]-->[Y])),
	length(X1, N), N1 is N+1.
rule([cll,e], no,  w(?), S, [S1], [r(N),[]]) :-
	match(S,  ([X]-->[Y1,[?_A],Y2])),
	match(S1, ([X]-->[Y1,Y2])),
	length(Y1, N).
rule([cll,e], inv, l(?), S, [S1], [l(N),l(N)]) :-
	match(S,  ([X1,[?A],X2]-->[Y])),
	all_ofcourse(X1), all_ofcourse(X2),
	all_whynot(Y),
	match(S1, ([X1,[A],X2]-->[Y])),
	length(X1, N).
rule([cll,e], no,  r(?), S, [S1], [r(N),r(N)]) :-
	match(S,  ([X]-->[Y1,[?A],Y2])),
	match(S1, ([X]-->[Y1,[A],Y2])),
	length(Y1, N).
rule([cll,e], no,  c(?), S, [S1], [r(N),[r(N),r(N1)]]) :-
	match(S,  ([X]-->[Y1,[?A],Y2])),
	match(S1, ([X]-->[Y1,[?A,?A],Y2])),
	length(Y1, N), N1 is N+1.
% Cut rule
rule([ill,0], no,  cut, S, [S1, S2], [[],r(0),l(0)]) :-
%	match(S,  ([X21,X1,X22]-->[Y11,Y2,Y12])),
%	match(S1, ([X1]-->[Y11,[C],Y12])),
%	match(S2, ([X21,[C],X22]-->[Y2])).
	match(S,  ([X]-->[Y])),
	match(S1, ([]-->[[C]])),
	match(S2, ([[C],X]-->[Y])).

all_ofcourse([]).
all_ofcourse([X|Xs]) :- nonvar(X), X = !_, all_ofcourse(Xs).

all_whynot([]).
all_whynot([X|Xs]) :- nonvar(X), X = ?_, all_whynot(Xs).

match((X-->Y), (P-->Q)) :- append_all(P, X), append_all(Q, Y).

eigen_variable(V, X) :-
	freeze(V, fail),
	free_variables(X, Us),
	dif_list(Us, V).

free_variables(X, Vs) :- free_vars(X, [], [], Vs).

free_vars(X, BVs, Vs0, Vs) :- var(X), !, free_vars1(X, BVs, Vs0, Vs).
free_vars(X, _BVs, Vs, Vs) :- ground(X), !.
free_vars([X|Y], BVs, Vs0, Vs) :- !,
	free_vars(X, BVs, Vs0, Vs1), free_vars(Y, BVs, Vs1, Vs).
free_vars(all(X,A), BVs, Vs0, Vs) :- !,
	free_vars(A, [X|BVs], Vs0, Vs).
free_vars(exists(X,A), BVs, Vs0, Vs) :- !,
	free_vars(A, [X|BVs], Vs0, Vs).
free_vars(X, BVs, Vs0, Vs) :- X =.. Y, free_vars(Y, BVs, Vs0, Vs).

free_vars1(X, BVs, Vs, Vs) :- (memq(X, BVs); memq(X, Vs)), !.
free_vars1(X, _BVs, Vs, [X|Vs]).

dif_list([], _).
dif_list([U|Us], V) :- dif(U, V), dif_list(Us, V).

%
%  Convert to Proof Net
%
convert_to_proofnet(P, Qs) :-
	conv_onesided(P, P1),
	conv_proofnet(P1, 1, _, Qs1),
	remove_nop_list(Qs1, Qs).

conv_proofnet([/\,_,_|_], _, _, _) :- !,
	fail.
conv_proofnet([Rule,[_],S0], M0, M, Qs) :- !,
	put_link_number(S0, Rule, M0, Qs),
	M is M0+1.
conv_proofnet([Rule,[N0,[N11,N12]],S0,P1], M0, M, Qs) :- !,
	P1 = [_,_,S1|_],
	get_nth_formula(N0, S0, A0),
	get_nth_formula(N11, S1, A11),
	get_nth_formula(N12, S1, A12),
	conv_proofnet(P1, M0, M, Qs1),
	select_proof(A11, Qs1, Q11, Qs2),
	select_proof(A12, Qs2, Q12, Qs3),
	Qs = [[Rule,0,[A0],Q11,Q12]|Qs3].
conv_proofnet([Rule,[N0,N1],S0,P1], M0, M, Qs) :- !,
	P1 = [_,_,S1|_],
	get_nth_formula(N0, S0, A0),
	get_nth_formula(N1, S1, A1),
	conv_proofnet(P1, M0, M, Qs1),
	select_proof(A1, Qs1, Q1, Qs2),
	Qs = [[Rule,0,[A0],Q1]|Qs2].
conv_proofnet([Rule,[N0,N1,N2],S0,P1,P2], M0, M, Qs) :- !,
	P1 = [_,_,S1|_],
	P2 = [_,_,S2|_],
	get_nth_formula(N0, S0, A0),
	get_nth_formula(N1, S1, A1),
	get_nth_formula(N2, S2, A2),
	conv_proofnet(P1, M0, M1, Qs1),
	conv_proofnet(P2, M1, M, Qs2),
	select_proof(A1, Qs1, Q1, Qs3),
	select_proof(A2, Qs2, Q2, Qs4),
	append(Qs3, Qs4, Qs5),
	Qs = [[Rule,0,[A0],Q1,Q2]|Qs5].

put_link_number([], _, _, []).
put_link_number([A|As], Rule, M, [[[Rule,M],[],[A]]|Qs]) :-
	put_link_number(As, Rule, M, Qs).

get_nth_formula([], _, []) :- !.
get_nth_formula(N, Xs, X) :- get_nth(N, Xs, X).

select_proof([], Qs, [], Qs) :- !.
select_proof(A, Qs0, Q, Qs) :-
	select_proof1(Qs0, A, Q, Qs).

select_proof1([], _, [], []).
select_proof1([Q|Qs], A, Q, Qs) :- Q = [_,_,[A0]|_], A==A0, !.
select_proof1([Q0|Qs0], A, Q, [Q0|Qs]) :- select_proof1(Qs0, A, Q, Qs).

%
%  Convert to one-sided
%
convert_to_onesided(P, Q) :-
	conv_onesided(P, P1),
	remove_nop(P1, Q).

remove_nop([], []).
remove_nop([nop,_,_,P1], Q) :- !,
	remove_nop(P1, Q).
remove_nop([Rule,Pos,[[]]|Ps], [Rule,Pos,[]|Qs]) :- !,
	remove_nop_list(Ps, Qs).
remove_nop([Rule,Pos,S|Ps], [Rule,Pos,S|Qs]) :- !,
	remove_nop_list(Ps, Qs).

remove_nop_list([], []).
remove_nop_list([[]|Ps], Qs) :- !,
	remove_nop_list(Ps, Qs).
remove_nop_list([P|Ps], [Q|Qs]) :-
	remove_nop(P, Q), remove_nop_list(Ps, Qs).

conv_onesided([], []).
conv_onesided([Rule0,Pos0,S0|Ps0], Q) :-
	conv_onesided(Rule0, Pos0, S0, Ps0, Q).

conv_onesided(Rule0, Pos0, S0, Ps0, [Rule,Pos,S|Ps]) :-
	conv_onesided_rule(Rule0, Rule),
	conv_onesided_pos(Rule0, Pos0, S0,Ps0,  Pos),
	conv_onesided_seq(S0, S),
	conv_onesided_list(Ps0, Ps).

conv_onesided_list([], []).
conv_onesided_list([P|Ps], [Q|Qs]) :-
	conv_onesided(P, Q),
	conv_onesided_list(Ps, Qs).

conv_onesided_pos(Rule0, Pos0, S0, Ps0, Pos) :-
	conv_pos_list(Pos0, [[Rule0,_,S0]|Ps0], Pos).

conv_pos_list([], [], []).
conv_pos_list([U|Us], [P|Ps], [V|Vs]) :-
	conv_pos(U, P, V),
	conv_pos_list(Us, Ps, Vs).

conv_pos([], _, []).
conv_pos([U|Us], P, [V|Vs]) :- !,
	conv_pos(U, P, V),
	conv_pos(Us, P, Vs).

conv_pos(l(N), _, N).
conv_pos(r(N), [_,_,(Xs-->_Ys)|_], N1) :-
	length(Xs, Off),
	N1 is N+Off.

% One-sided rules are: axiom, ax, cut, *, /\, (\/,1), (\/,2), +
% 0, top, 1, all, exists, c(?), w(?), d(?), !
conv_onesided_rule(l(~), nop) :- !.
conv_onesided_rule(r(~), nop) :- !.
conv_onesided_rule(w(!), w(?)) :- !.
conv_onesided_rule(l(!), d(?)) :- !.
conv_onesided_rule(r(!), !) :- !.
conv_onesided_rule(c(!), c(?)) :- !.
conv_onesided_rule(w(?), w(?)) :- !.
conv_onesided_rule(l(?), !) :- !.
conv_onesided_rule(r(?), d(?)) :- !.
conv_onesided_rule(c(?), c(?)) :- !.
conv_onesided_rule(l(->), *) :- !.
conv_onesided_rule(r(->), +) :- !.
conv_onesided_rule(r(X), X) :- !.
conv_onesided_rule(r(X,N), (X,N)) :- !.
conv_onesided_rule(l(X), Z) :- !, de_morgan_dual(X, Z).
conv_onesided_rule(l(X,N), (Z,N)) :- !, de_morgan_dual(X, Z).
conv_onesided_rule(X, X).

conv_onesided_seq((Xs-->Ys), Zs) :-
	neg0_list(Ys, Ys1),
	neg1_list(Xs, Xs1),
	append(Xs1, Ys1, Zs).

neg0_list([], []).
neg0_list([A|As], [U|Us]) :- neg0_formula(A, U), neg0_list(As, Us).

neg1_list([], []).
neg1_list([A|As], [U|Us]) :- neg1_formula(A, U), neg1_list(As, Us).

neg0_formula(~A, U) :- !, neg1_formula(A, U).
neg0_formula(A/\B, U/\V) :- !, neg0_formula(A, U), neg0_formula(B, V).
neg0_formula(A*B, U*V) :- !, neg0_formula(A, U), neg0_formula(B, V).
neg0_formula(A\/B, U\/V) :- !, neg0_formula(A, U), neg0_formula(B, V).
neg0_formula(A+B, U+V) :- !, neg0_formula(A, U), neg0_formula(B, V).
neg0_formula(A->B, U+V) :- !, neg1_formula(A, U), neg0_formula(B, V).
neg0_formula(all(X,A), all(X,U)) :- !, neg0_formula(A, U).
neg0_formula(exists(X,A), exists(X,U)) :- !, neg0_formula(A, U).
neg0_formula(!A, !U) :- !, neg0_formula(A, U).
neg0_formula(?A, ?U) :- !, neg0_formula(A, U).
neg0_formula(A, A).

neg1_formula(~A, U) :- !, neg0_formula(A, U).
neg1_formula(A/\B, U\/V) :- !, neg1_formula(A, U), neg1_formula(B, V).
neg1_formula(A*B, U+V) :- !, neg1_formula(A, U), neg1_formula(B, V).
neg1_formula(A\/B, U/\V) :- !, neg1_formula(A, U), neg1_formula(B, V).
neg1_formula(A+B, U*V) :- !, neg1_formula(A, U), neg1_formula(B, V).
neg1_formula(A->B, U*V) :- !, neg0_formula(A, U), neg1_formula(B, V).
neg1_formula(all(X,A), exists(X,U)) :- !, neg1_formula(A, U).
neg1_formula(exists(X,A), all(X,U)) :- !, neg1_formula(A, U).
neg1_formula(!A, ?U) :- !, neg1_formula(A, U).
neg1_formula(?A, !U) :- !, neg1_formula(A, U).
neg1_formula(A, U) :- de_morgan_dual(A, U), !.
neg1_formula(A, ~A).

de_morgan_dual(X, Z) :- de_morgan_dual0(X, Z), !.
de_morgan_dual(X, Z) :- de_morgan_dual0(Z, X), !.

de_morgan_dual0(0, 1).
de_morgan_dual0(bot, top).
de_morgan_dual0(+, *).
de_morgan_dual0(\/, /\).
de_morgan_dual0(exists, all).
de_morgan_dual0(?, !).

%
%  Standard form printer
%
standard_print(twosided(P)) :- !,
	standard_print(P, 0).
standard_print(onesided(P)) :- !,
	standard_print(P, 0).
standard_print(proofnet(Ps)) :- !,
	standard_print_list(Ps, 0).

standard_print([Rule,_,S|Ps], Tab) :-
	tabx(Tab),
	write_rule_name(Rule), writex(': '),
	write_seq(S), nlx,
	Tab1 is Tab+2,
	standard_print_list(Ps, Tab1).

standard_print_list([], _).
standard_print_list([P|Ps], Tab) :-
	standard_print(P, Tab), standard_print_list(Ps, Tab).

%
%  Pretty form printer
%
pretty_print(P0) :-
	name_variables(P0, P),
	pretty_print1(P),
	fail.
pretty_print(_).

pretty_print1(twosided(P)) :- !,
	place_proof(P, [], Q, _, _),
	print_placed_proof(Q).
pretty_print1(onesided(P)) :- !,
	place_proof(P, [], Q, _, _),
	print_placed_proof(Q).
pretty_print1(proofnet(Ps)) :- !,
	place_proof_list(Ps, [], Qs, _, _),
	print_placed_proofs(Qs).

name_variables(X, Z) :-
	name_variables(X, 0, _N, [], _Vs, Z).

name_variables(X, N, N, Vs, Vs, X) :- ground(X), !.
name_variables(X, N, N, Vs, Vs, Z) :- var(X), assoc(X, Z, Vs), !.
name_variables(X, N0, N, Vs0, [[X|Z]|Vs0], Z) :- var(X), !,
	V is N0 mod 3, VN is N0//3,
	name_var(V, VN, Z),
	N is N0+1.
name_variables([X|Xs], N0, N, Vs0, Vs, [Z|Zs]) :- !,
	name_variables(X, N0, N1, Vs0, Vs1, Z),
	name_variables(Xs, N1, N, Vs1, Vs, Zs).
name_variables(X, N0, N, Vs0, Vs, Z) :-
	X =.. Xs,
	name_variables(Xs, N0, N, Vs0, Vs, Zs),
	Z =.. Zs.

name_var(0, VN, X) :- !, name_var1("X", VN, X).
name_var(1, VN, X) :- !, name_var1("Y", VN, X).
name_var(2, VN, X) :- !, name_var1("Z", VN, X).

name_var1([V], 0, X) :- !, name(X, [V]).
name_var1([V], VN, X) :-
	name(VN, Ns),
	name(X, [V|Ns]).

%
%  place_proof(+Proof, +Margins,
%              -Proof_with_pos, -LowerLeftPos, -NewMargins)
%
place_proof([Rule,_,S|Ps1], Ms0, Q, LowerPos, Ms) :-
	get_margins([M0,M1|Ms1], Ms0),
	place_uppers(Ps1, Ms1, Ps2, UpperPos0, Ms2),
	get_margins([M2|_], Ms2),
	UpperWidth is M2-UpperPos0,
	get_rule_name_width(Rule, W1),
	get_seq_width(S, LowerWidth),
	LowerOff is max(0,max(UpperPos0,max(M1,M0))-UpperPos0),
	RulePos is UpperPos0+LowerOff,
	RuleWidth is max(UpperWidth,LowerWidth),
	LowerPos is RulePos+(RuleWidth-LowerWidth)//2,
	UpperPos is max(UpperPos0,RulePos),
	UpperOff is UpperPos-UpperPos0,
	move_proof_list(Ps2, UpperOff, Ps3),
	move_margins(Ms2, UpperOff, Ms3),
	new_rule_width(Rule, RuleWidth, W1, RuleWidth1, W2),
	Q = [RulePos+RuleWidth1,Rule,LowerPos+LowerWidth,S|Ps3],
	M11 is RulePos+RuleWidth1+W2,
	M01 is LowerPos+LowerWidth,
	Ms = [M01,M11|Ms3].

new_rule_width([_Rule,_], _, W1, 0, W1) :- !.
new_rule_width(_Rule, RW, W1, RW, W2) :- W2 is W1+1.

place_uppers(Ps, Ms0, Qs, T, Ms) :-
	place_proof_list(Ps, Ms0, Qs, T, Ms).

place_proof_list([], Ms0, [], T, Ms0) :- !,
	get_margins([T|_], Ms0).
place_proof_list([P1], Ms0, [Q1], T, Ms) :- !,
	place_proof(P1, Ms0, Q1, T, Ms).
place_proof_list([P1|Ps], Ms0, [Q1|Qs], T, Ms) :-
	place_proof(P1, Ms0, Q1, T, Ms1),
	move_margins(Ms1, 2, Ms2),
	place_proof_list(Ps, Ms2, Qs, _T1, Ms).

move_proof_list([], _, []).
move_proof_list([P0|Ps0], Off, [P|Ps]) :-
	move_proof(P0, Off, P),
	move_proof_list(Ps0, Off, Ps).

move_proof([M0+W0,Rule,M1+W1,S|Ps0], Off, [N0+W0,Rule,N1+W1,S|Ps]) :-
	N0 is M0+Off, N1 is M1+Off,
	move_proof_list(Ps0, Off, Ps).

get_margins(Zs, Xs) :- var(Zs), !, Zs=Xs.
get_margins([], _).
get_margins([Z|Zs], []) :- !, Z=0, get_margins(Zs, []).
get_margins([Z|Zs], [Z|Xs]) :- get_margins(Zs, Xs).

move_margins([], _, []).
move_margins([M0|Ms0], Off, [M|Ms]) :-
	M is M0+Off, move_margins(Ms0, Off, Ms).

%
%  print_placed_proof(+Placed_Proof)
%
print_placed_proof(P) :-
	print_placed_proofs([P]).

print_placed_proofs([]).
print_placed_proofs(Ps) :- Ps=[_|_],
	gather_uppers(Ps, Qs),
	print_placed_proofs(Qs),
	print_rules(Ps),
	nlx,
	print_lowers(Ps),
	nlx.

gather_uppers([], []).
gather_uppers([P|Ps], Qs) :-
	gather_uppers(Ps, Qs1),
	P = [_,_Rule,_,_S|P0],
	append(P0, Qs1, Qs).

print_rules([]).
print_rules([P|Ps]) :-
	P = [M0+W0,Rule,_M1+_W1,_S|_],
	goto_pos(M0),
	print_rule_line(W0),
	write_rule_name(Rule),
	print_rules(Ps).

print_rule_line(0) :- !.
print_rule_line(N) :- N>0, n_writex(N, '-'), writex(' ').

print_lowers([]).
print_lowers([P|Ps]) :-
	P = [_M0+_W0,_Rule,M1+_W1,S|_],
	goto_pos(M1),
	write_seq(S),
	print_lowers(Ps).

get_width(X, W) :-
	open_null(NULL, OldSTR, OldLog),
	nlx,
	writex(X),
	line_position(W),
	close_null(NULL, OldSTR, OldLog).

get_rule_name_width(R, W) :-
	open_null(NULL, OldSTR, OldLog),
	nlx,
	write_rule_name(R),
	line_position(W),
	close_null(NULL, OldSTR, OldLog).

get_seq_width(S, W) :-
	open_null(NULL, OldSTR, OldLog),
	nlx,
	write_seq(S),
	line_position(W),
	close_null(NULL, OldSTR, OldLog).

open_null(NULL, OldSTR, OldLog) :-
	current_output(OldSTR),
	open_null_stream(NULL),
	set_output(NULL),
	log_suspend(OldLog).

close_null(NULL, OldSTR, OldLog) :-
	set_output(OldSTR),
	close(NULL),
	log_resume(OldLog).

write_rule_name(axiom) :- !, writex('Axiom').
write_rule_name(ax) :- !, writex('Ax').
write_rule_name(cut) :- !, writex('Cut').
write_rule_name(r(R)) :- !, writex('R'), writex(R).
write_rule_name(r(R,N)) :- !, writex('R'), writex(R), writex(N).
write_rule_name(l(R)) :- !, writex('L'), writex(R).
write_rule_name(l(R,N)) :- !, writex('L'), writex(R), writex(N).
write_rule_name(c(R)) :- !, writex('C'), writex(R).
write_rule_name(w(R)) :- !, writex('W'), writex(R).
% added for one-sided
write_rule_name(d(R)) :- !, writex('D'), writex(R).
write_rule_name((R,N)) :- !, writex(R), writex(N).
% added for proofnet
write_rule_name([R,LN]) :- !,
	write_rule_name(R), writex('('), writex(LN), writex(')').
write_rule_name(R) :- writex(R).

write_seq((Xs-->Ys)) :- !,
	write_list(Xs), writex(' --> '), write_list(Ys).
% added for one-sided
write_seq(Xs) :- !,
	write_list(Xs).

write_list([]).
write_list([X]) :- !, writex(X).
write_list([X|Xs]) :- writex(X), writex(','), write_list(Xs).

%
%  Tex form printer
%
tex_print(twosided(P)) :- !,
	tex_name_variables(P, Q),
	writex('\\begin{displaymath}'), nlx,
	tex_print(0, Q),
	writex('\\end{displaymath}'), nlx.
tex_print(onesided(P)) :- !,
	tex_name_variables(P, Q),
	writex('\\begin{displaymath}'), nlx,
	tex_print(0, Q),
	writex('\\end{displaymath}'), nlx.
tex_print(proofnet(Ps)) :- !,
	tex_name_variables(Ps, Qs),
	writex('\begin{displaymath}'), nlx,
	length(Qs, N),
	writex('\begin{array}{'), n_writex(N, 'c'), writex('}'),
	tex_print_list(Qs, 0),
	writex('\end{array}'), nlx,
	writex('\end{displaymath}'), nlx.

tex_name_variables(X, Z) :-
	tex_name_variables(X, 0, _N, [], _Vs, Z).

tex_name_variables(X, N, N, Vs, Vs, X) :- ground(X), !.
tex_name_variables(X, N, N, Vs, Vs, Z) :- var(X), assoc(X, Z, Vs), !.
tex_name_variables(X, N0, N, Vs0, [[X|Z]|Vs0], Z) :- var(X), !,
	V is N0 mod 3, VN is N0//3,
	tex_name_var(V, VN, Z),
	N is N0+1.
tex_name_variables([X|Xs], N0, N, Vs0, Vs, [Z|Zs]) :- !,
	tex_name_variables(X, N0, N1, Vs0, Vs1, Z),
	tex_name_variables(Xs, N1, N, Vs1, Vs, Zs).
tex_name_variables(X, N0, N, Vs0, Vs, Z) :-
	X =.. Xs,
	tex_name_variables(Xs, N0, N, Vs0, Vs, Zs),
	Z =.. Zs.

tex_name_var(0, VN, X) :- !, tex_name_var1("x", VN, X).
tex_name_var(1, VN, X) :- !, tex_name_var1("y", VN, X).
tex_name_var(2, VN, X) :- !, tex_name_var1("z", VN, X).

tex_name_var1([V], 0, X) :- !, name(X, [V]).
tex_name_var1([V], VN, X) :-
	[C1,C2]="_{",
	name(VN, Ns), append(Ns, "}", Ns1),
	name(X, [V,C1,C2|Ns1]).

tex_print(Tab, [[Rule,LN],_,S]) :- !,
	tabx(Tab), writex('\\deduce{'),
	tex_print_sequent(S), writex('}{'),
	tex_print_rule_name([Rule,LN]),	writex('}'), nlx.
tex_print(Tab, [Rule,_,S|Ss]) :-
	tabx(Tab), writex('\\infer['),
	tex_print_rule_name(Rule), writex(']{'),
	tex_print_sequent(S),
	writex('}{'),
	tex_print_list(Ss, Tab),
	writex('}'), nlx.

tex_print_list([], _Tab).
tex_print_list([S1], Tab) :- !,
	nlx,
	Tab1 is Tab+2,
	tex_print(Tab1, S1),
	tabx(Tab).
tex_print_list([S1|Ss], Tab) :- !,
	nlx,
	Tab1 is Tab+2,
	tex_print(Tab1, S1),
	tabx(Tab1), writex('&'),
	tex_print_list(Ss, Tab).

tex_print_sequent((Xs-->Ys)) :- !,
	tex_print_formulas(Xs),
	writex(' \\drv '),
	tex_print_formulas(Ys).
% added for one-sided
tex_print_sequent(Xs) :-
	tex_print_formulas(Xs).

tex_print_formulas([]).
tex_print_formulas([A]) :- !,
	tex_print_formula(A).
tex_print_formulas([A|As]) :-
	tex_print_formula(A),
	writex(', '),
	tex_print_formulas(As).

tex_print_formula(A) :-
	tex_print_formula(999, A).

tex_print_formula(Prec0, A) :- is_op(A, Prec, Type, Op, As), !,
	(Prec0 < Prec -> writex('('); true),
	tex_print_op_formula(Prec, Type, Op, As),
	(Prec0 < Prec -> writex(')'); true),
	!.
tex_print_formula(Prec0, A) :- tex_quantifier_name(A, Q, X, B), !,
	Prec = 999,
	(Prec0 < Prec -> writex('('); true),
	writex(Q), writex(' '), writex(X), writex('.'),
	tex_print_formula(B),
	(Prec0 < Prec -> writex(')'); true),
	!.
tex_print_formula(_Prec0, A) :- tex_unit_name(A, U), !,
	writex(U).
tex_print_formula(_Prec0, A) :-
	rename_functor(A, A1),
	writex(A1).

rename_functor(X, Z) :-
	X =.. [F0|As],
	capitalize_atom(F0, F),
	Z =.. [F|As].

tex_quantifier_name(all(X,A), '\\lall', X, A).
tex_quantifier_name(exists(X,A), '\\lexists', X, A).

tex_unit_name(0, '\\tzero').
tex_unit_name(1, '\\tunit').
tex_unit_name(bot, '\\dzero').
tex_unit_name(top, '\\dunit').

tex_print_op_formula(Prec, fy, Op, [A1]) :- Op = ~, !,
	tex_print_op(Op), writex('{'),
	tex_print_formula(Prec, A1), writex('}').
tex_print_op_formula(Prec, fx, Op, [A1]) :- !,
	Prec1 is Prec - 1,
	tex_print_op(Op), writex(' '),
	tex_print_formula(Prec1, A1).
tex_print_op_formula(Prec, fy, Op, [A1]) :- !,
	tex_print_op(Op), writex(' '),
	tex_print_formula(Prec, A1).
tex_print_op_formula(Prec, xf, Op, [A1]) :- !,
	Prec1 is Prec - 1,
	tex_print_formula(Prec1, A1),
	writex(' '), tex_print_op(Op).
tex_print_op_formula(Prec, yf, Op, [A1]) :- !,
	tex_print_formula(Prec, A1),
	writex(' '), tex_print_op(Op).
tex_print_op_formula(Prec, xfx, Op, [A1,A2]) :- !,
	Prec1 is Prec - 1,
	tex_print_formula(Prec1, A1),
	writex(' '), tex_print_op(Op), writex(' '),
	tex_print_formula(Prec1, A2).
tex_print_op_formula(Prec, xfy, Op, [A1,A2]) :- !,
	Prec1 is Prec - 1,
	tex_print_formula(Prec1, A1),
	writex(' '), tex_print_op(Op), writex(' '),
	tex_print_formula(Prec, A2).
tex_print_op_formula(Prec, yfx, Op, [A1,A2]) :- !,
	Prec1 is Prec - 1,
	tex_print_formula(Prec, A1),
	writex(' '), tex_print_op(Op), writex(' '),
	tex_print_formula(Prec1, A2).

is_op(A, Prec, Type, Op, As) :-
	functor(A, Op, N), current_op(Prec, Type, Op),
	is_op0(A, Type, N, As),
	!.
is_op0(A, fx, 1, [A1]) :- arg(1, A, A1).
is_op0(A, fy, 1, [A1]) :- arg(1, A, A1).
is_op0(A, xf, 1, [A1]) :- arg(1, A, A1).
is_op0(A, yf, 1, [A1]) :- arg(1, A, A1).
is_op0(A, xfx, 2, [A1,A2]) :- arg(1, A, A1), arg(2, A, A2).
is_op0(A, xfy, 2, [A1,A2]) :- arg(1, A, A1), arg(2, A, A2).
is_op0(A, yfx, 2, [A1,A2]) :- arg(1, A, A1), arg(2, A, A2).

tex_print_op(Op) :-
	tex_op_name(Op, OpName), !,
	writex(OpName).

tex_op_name(~,  '\\lnot').
tex_op_name(*,  '\\tprod').
tex_op_name(/\, '\\dprod').
tex_op_name(+,  '\\tsum').
tex_op_name(\/, '\\dsum').
tex_op_name(->, '\\limp').
tex_op_name(!,  '!').
tex_op_name(?,  '?').

tex_print_rule_name([Rule,LN]) :- !,
	tex_rule_name(Rule, RuleName),
	!,
	writex(RuleName),
	writex('('), writex(LN), writex(')').
tex_print_rule_name(Rule) :-
	tex_rule_name(Rule, RuleName),
	!,
	writex(RuleName).

tex_rule_name(ax, '\\Ax').
tex_rule_name(axiom, '\\Axiom').
tex_rule_name(l(1), '\\LR{\\tunit}').
tex_rule_name(r(1), '\\RR{\\tunit}').
tex_rule_name(r(top), '\\RR{\\dunit}').
tex_rule_name(r(0), '\\RR{\\tzero}').
tex_rule_name(l(0), '\\LR{\\tzero}').
tex_rule_name(l(bot), '\\LR{\\dzero}').
tex_rule_name(l(~), '\\LR{\\lnot{}}').
tex_rule_name(r(~), '\\RR{\\lnot{}}').
tex_rule_name(l(/\,1), '\\LR{\\dprod_{1}}').
tex_rule_name(l(/\,2), '\\LR{\\dprod_{2}}').
tex_rule_name(r(/\), '\\RR{\\dprod}').
tex_rule_name(l(*), '\\LR{\\tprod}').
tex_rule_name(r(*), '\\RR{\\tprod}').
tex_rule_name(l(\/), '\\LR{\\dsum}').
tex_rule_name(r(\/,1), '\\RR{\\dsum_{1}}').
tex_rule_name(r(\/,2), '\\RR{\\dsum_{2}}').
tex_rule_name(l(+), '\\LR{\\tsum}').
tex_rule_name(r(+), '\\RR{\\tsum}').
tex_rule_name(l(->), '\\LR{\\limp}').
tex_rule_name(r(->), '\\RR{\\limp}').
tex_rule_name(l(all), '\\LR{\\lall}').
tex_rule_name(r(all), '\\RR{\\lall}').
tex_rule_name(l(exists), '\\LR{\\lexists}').
tex_rule_name(r(exists), '\\RR{\\lexists}').
tex_rule_name(w(!), '\\WR{!}').
tex_rule_name(l(!), '\\LR{!}').
tex_rule_name(r(!), '\\RR{!}').
tex_rule_name(c(!), '\\CR{!}').
tex_rule_name(w(?), '\\WR{?}').
tex_rule_name(l(?), '\\LR{?}').
tex_rule_name(r(?), '\\RR{?}').
tex_rule_name(c(?), '\\CR{?}').
tex_rule_name(cut, '\\Cut').
% added for one-sided
tex_rule_name(*, '\\tprod').
tex_rule_name(/\, '\\dprod').
tex_rule_name((\/,1), '\\dsum_{1}').
tex_rule_name((\/,2), '\\dsum_{2}').
tex_rule_name(+, '\\tsum').
tex_rule_name(0, '\\tzero').
tex_rule_name(top, '\\dunit').
tex_rule_name(1, '\\tunit').
tex_rule_name(all, '\\lall').
tex_rule_name(exists, '\\lexists').
tex_rule_name(d(?), '\\DR{?}').
tex_rule_name(!, '!').

%
%  Utilities
%
append_all([], []).
append_all([P], P).
append_all([P|Ps], X) :- Ps=[_|_], append(P, X1, X), append_all(Ps, X1).

merge(X1, X2, X) :- split(X, X1, X2).

split([], [], []).
split([X|Xs], [X|Ys], Zs) :- split(Xs, Ys, Zs).
split([X|Xs], Ys, [X|Zs]) :- split(Xs, Ys, Zs).

append([], Z, Z).
append([W|X], Y, [W|Z]) :- append(X, Y, Z).

member(X, [X|_Xs]).
member(X, [_Y|Xs]) :- member(X, Xs).

memberq(X, [X|_Xs]) :- !.
memberq(X, [_Y|Xs]) :- memberq(X, Xs).

memq(X, [Y|_Xs]) :- X==Y, !.
memq(X, [_Y|Xs]) :- memq(X, Xs).

get_nth(0, [X|_Xs], X) :- !.
get_nth(N, [_|Xs], X) :- N>0, N1 is N-1, get_nth(N1, Xs, X).

for(I, M, N) :- M =< N, I=M.
for(I, M, N) :- M =< N, M1 is M+1, for(I, M1, N).

assoc(X, Z, [[X0|Z]|_As]) :- X==X0, !.
assoc(X, Z, [_|As]) :- assoc(X, Z, As).

substitute(X0, X, A0, A) :- var(A0), X0==A0, !, A=X.
substitute(_X0, _X, A0, A) :- var(A0), !, A=A0.
substitute(_X0, _X, A0, A) :- atomic(A0), !, A=A0.
substitute(X0, X, [A0|B0], [A|B]) :- !,
	substitute(X0, X, A0, A),
	substitute(X0, X, B0, B).
substitute(X0, X, A0, A) :-
	A0 =.. B0,
	substitute(X0, X, B0, B),
	A =.. B.

capitalize_atom(X, Z) :- atom(X),
	name(X, [C0|Cs]), C0 >= "a", C0 =< "z", !,
	C is ((C0 - "a") + "A"),
	name(Z, [C|Cs]).
capitalize_atom(X, X).

n_writex(0, _) :- !.
n_writex(N, X) :- N>0, writex(X), N1 is N-1, n_writex(N1, X).

flush_out :-
	current_output(S),
	flush_output(S).

goto_pos(T) :-
	current_output(S),
	line_position(S, T0),
	tabx(T-T0).

line_position(W) :-
	current_output(S),
	line_position(S, W).

%
%  Logging
%
log_start(yes) :- !,
	log_start('llprover.log').
log_start(File) :-
	logging(no, _),
	!,
	open(File, write, STR),
	retractall(logging(_,_)),
	assert(logging(File, STR)).

log_end :-
	logging(no, _),
	!.
log_end :-
	logging(_File, STR),
	close(STR),
	fail.
log_end :-
	retractall(logging(_,_)),
	assert(logging(no, _)).

log_suspend(logging(File,STR)) :-
	logging(File, STR),
	retractall(logging(_,_)),
	assert(logging(no, _)).

log_resume(logging(File,STR)) :-
	retractall(logging(_,_)),
	assert(logging(File, STR)).

readx(STR, X) :-
	read(STR, X),
	echo_read(STR, X).

echo_read(user_input, _X) :-
	logging(no, _),
	!.
echo_read(user_input, X) :-
	logging(_File, STR),
	!,
	write(STR, X),
	write(STR, '.'),
	nl(STR).
echo_read(_, X) :-
	writex(X),
	writex('.'),
	nlx.

writex(X) :-
	logging(no, _),
	!,
	write(X).
writex(X) :-
	logging(_, STR),
	write(X),
	write(STR, X).

nlx :-
	logging(no, _),
	!,
	nl.
nlx :-
	logging(_, STR),
	nl,
	nl(STR).

tabx(X) :-
	logging(no, _),
	!,
	tab(X).
tabx(X) :-
	logging(_, STR),
	tab(X),
	tab(STR, X).

%
%  Initialization
%
:- ll_init.
