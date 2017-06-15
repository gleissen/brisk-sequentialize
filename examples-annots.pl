

/*=====================
warmup: simple loops
=====================*/


rewrite_query(T, skip, _, Name) :-
	P1=for(p, Q, q, send(p, e_pid(Q), p)),
	P2=recv(Q, e_pid(p), id),
	T=(par([P1, sym(Q, q, P2)])),
	Name=for-send.


rewrite_query(T, skip, _, Name) :-
	P1=for(p, _, q, recv(p, e_pid(q), id)),
	P2=send(Q, e_pid(p), Q),
	T=(par([P1, sym(Q, q, P2)])),
	Name=for-recv.


rewrite_query(T, skip, _, Name) :-
	P1=for(p, Q, q, seq([send(p, e_pid(Q), p), recv(p, e_pid(Q), id)])),
	P2=seq([recv(Q, e_pid(p), id),send(Q, e_pid(p), Q)]),
	T=(par([P1, sym(Q, q, P2)])),
	Name=for-ping.

rewrite_query(T, skip, _, Name) :-
	P1=for(p, _, q, seq([recv(p, e_pid(q), id), send(p, e_var(id), p)])),
	P2=seq([send(Q, e_pid(p), Q), recv(Q, e_pid(p), id)]),
	T=(par([P1, sym(Q, q, P2)])),
	Name=for-reverse-ping.

rewrite_query(T, skip, _, Name) :-
	P1=for(p, Q, q, seq([send(p, e_pid(Q), p), recv(p, e_pid(q), id)])),
	P2=seq([recv(Q, e_pid(p), id),send(Q, e_pid(p), Q)]),
	T=(par([P1, sym(Q, q, P2)])),
	Name=for-ping-error.

/*
Fixme
rewrite_query(T, skip, _, Name) :-
	P1=for(p, Q1, q, seq([recv(p, e_pid(q), id), send(p, e_pid(Q1), p)])),
	P2=seq([send(Q, e_pid(p), Q), recv(Q, e_pid(p), id)]),
	T=(par([P1, sym(Q, q, P2)])),
	Name=for-reverse-ping-error.
*/
/*======================
residual-fors
======================*/

rewrite_query(T, skip, _, Name) :-
	P1=seq([send(p, e_pid(q), p)]),
	P2=seq([for(q, P, {p}, recv(q, e_pid({P}), id))
		]),
	T=(par([P1, P2])),
	Name=resid-for-ping.

rewrite_query(T, skip, _, Name) :-
	P1=seq([send(p, e_pid(q), p), recv(p, e_pid(q), id)]),
	P2=for(q, _, {p},
	       seq([
		    recv(q, e_pid({p}), id),
		    send(q, e_var(id), q)
		   ])
	      ),
	T=(par([P1, P2])),
	Name=resid-for-1.

rewrite_query(T, skip, _, Name) :-
	P1=seq([recv(p, e_pid(q), id), send(p, e_var(id), p)]),
	P2=for(q, P, {p},
	       seq([
		    send(q, e_pid(P), q),
		    recv(q, e_pid(P), id)
		   ])
	      ),
	T=(par([P1, P2])),
	Name=resid-for-rev-1.

rewrite_query(T, skip, _, Name) :-
	P1=seq([recv(p, e_pid(q), id), send(p, e_var(id), p)]),
	P2=seq([for(q, P, {p}, send(q, e_pid(P), q)),
		for(q, P, {p}, recv(q, e_pid({p}), id))
		]),
	T=(par([P1, P2])),
	Name=resid-for-2.

rewrite_query(T, skip, _, Name) :-
	P1=seq([recv(p, e_pid(q), id), send(p, e_var(id), p)]),
	P2=for(q, P, {p},
	       seq([
		    send(q, e_pid(P), q),
		    recv(q, e_pid({p}), id)
		   ])
	      ),
	T=(par([P1, P2])),
	Name=resid-for-1-error.

/*======================
residual-fors-in-loop
======================*/

rewrite_query(T, skip, _, Name) :-
	P1=for(p, Q1, q, send(p, e_pid(Q1), p)),
	P2=for(Q, _, {p}, recv(Q, e_pid({p}), id)),
	T=(par([P1, sym(Q, q, P2)])),
	Name=resid-for-ping-loop.


rewrite_query(T, skip, _, Name) :-
	P1=for(p, Q1, q, seq([send(p, e_pid(Q1), p), recv(p, e_pid(Q1), id)])),
	P2=for(Q, _, {p},
	       seq([
		    recv(Q, e_pid({p}), id),
		    send(Q, e_var(id), Q)
		   ])
	      ),
	T=(par([P1, sym(Q, q, P2)])),
	Name=resid-for-1-loop.

rewrite_query(T, skip, _, Name) :-
	P1=for(p, _, q, seq([
			     recv(p, e_pid(q), id),
			     send(p, e_var(id), p)
			    ])
	      ),
	P2=seq([
		for(Q, P, {p}, send(Q, e_pid(P), Q)),
		for(Q, _, {p}, recv(Q, e_pid({p}), id))
		]),
	T=(par([P1, sym(Q, q, P2)])),
	Name=resid-for-2-loop.


/*========
Broadcasts
==========*/
/*---------------
Broadcast ping:
---------------

Π(p:P)
for q in Q do
  send q p
end

||

Π(q:Q)
for p in P do
  _ <- recv(P)
end
*/
rewrite_query(T, skip, _, Name) :-
	P1=for(P, Q, q, send(P, e_pid(Q), P)),
	P2=for(Q, _, p, recv(Q, e_pid(p), id)),
	T=(par([sym(P, p, P1), sym(Q, q, P2)])),
	Name=broadcast-send.


rewrite_query(T, skip, _, Name) :-
	P1=for(P, Q, q,
	       seq([
		    send(P, e_pid(Q), P),
		    recv(P, e_pid(Q), id)
		   ])
	      ),	
	P2=for(Q, _, p,
	       seq([
		    recv(Q, e_pid(p), id),
		    send(Q, e_var(id), Q)
		   ])
	      ),
	T=(par([sym(P, p, P1), sym(Q, q, P2)])),
	Name=broadcast-ping.


rewrite_query(T, skip, _, Name) :-
	P1=for(p, _, q, seq([
			     recv(p, e_pid(q), id),
			     send(p, e_var(id), p)
			    ])
	      ),
	P2=seq([
		for(Q, P, {p}, send(Q, e_pid(P), Q)),
		for(Q, _, {p}, recv(Q, e_pid({p}), id))
		]),
	T=(par([P1, sym(Q, q, P2)])),
	Name=resid-for-2-loop.

rewrite_query(T, skip, _, Name) :-
	P1=for(P, _, q,
	       seq([
		    recv(P, e_pid(q), id),
		    send(P, e_var(id), p)
		   ])
	      ),	
	P2=seq([
		for(Q, P, p, send(Q, e_pid(P), Q)),
		for(Q, _, p, recv(Q, e_pid(p), id))
	       ]),
	T=(par([sym(P, p, P1), sym(Q, q, P2)])),
	Name=broadcast-reverse-ping.

/*========
Benchmarks
==========*/

/*-----
Simple
-----*/

rewrite_query(T, skip, _, Name) :-
	P1=for(m, Q, q, send(m, e_pid(Q), m)),
	P2=recv(Q, e_pid(m), id),
	T=(par([P1, sym(Q, q, P2)])),
	Name=simple.

/*---
2PC 
---*/

rewrite_query(T, skip, _, Name) :-
	P1=seq([assign(c, abort, 0),
		assign(c, commited, 0),
		for(c, P, p,
		    seq([
			 send(c, e_pid(P), pair(c,prop)),
			 recv(c, e_pid(P), msg),
			 ite(c, msg=1, assign(c, abort, 1), skip)
			])
		   ),
		ite(c, abort=0, seq([
				     assign(c,reply,1),
				     assign(c,committed,1)
				    ]),
		    assign(c, reply, 0)
		   ),
		for(c, P, p,
		    seq([
			 send(c, e_pid(P), pair(c,reply)),
			 recv(c, e_pid(P), ack)
			])
		   )
	       ]),
	
	P2=seq([
		assign(P, value, bottom),
		recv(P, e_pid(c), pair(id, val)),
		ite(c, ndet,
			 assign(P, msg, 0),
			 assign(P, msg, 1)
		   ),
		send(P, e_var(id), msg),
		recv(P, e_pid(c), pair(id, decision)),
		ite(P, decision=1, assign(P, value, val), skip),
		send(P, e_var(id), ack)
	       ]),
	T=(par([P1, sym(P, p, P2)])),
	Name=two-pc.
