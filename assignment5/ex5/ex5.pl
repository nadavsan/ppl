/*
 * **********************************************
 * Printing result depth
 *
 * You can enlarge it, if needed.
 * **********************************************
 */
maximum_printing_depth(100).

:- current_prolog_flag(toplevel_print_options, A),
   (select(max_depth(_), A, B), ! ; A = B),
   maximum_printing_depth(MPD),
   set_prolog_flag(toplevel_print_options, [max_depth(MPD)|B]).

% Signature: unique(List, UniqueList, Dups)/3
% Purpose: succeeds if and only if UniqueList contains the same elements of List without duplicates (according to their order in List), and Dups contains the duplicates
member(X,[X|_Xs]).
member(X,[_Y|Ys]):-member(X,Ys).
unique(Xs,Ys,Zs):-unique2(Xs,Ys,Zs,[]).
unique2([],[],[],_Ws).
unique2([X|Xs],Ys,[X|Zs],Ws):-unique2(Xs,Ys,Zs,Ws),member(X,Ws).
unique2([X|Xs],[X|Ys],Zs,Ws):-unique2(Xs,Ys,Zs,[X|Ws]),\+member(X,Ws).
