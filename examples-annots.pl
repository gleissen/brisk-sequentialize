

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
For-repeat
==========*/

rewrite_query(T, while(q, true, P2), _, Name) :-
	P1=for(p, _, x, send(p, e_pid(q), p)),
	P2=recv(q, e_pid(p), id),
	T=(par([P1,  while(q, true, P2)])),
	Name=send-for-while.

rewrite_query(T, while(q, true, P2), _, Name) :-
	P1=for(p, _, x,
	       seq([
		    send(p, e_pid(q), p),
		    send(p, e_pid(q), p)
		   ])
	      ),
        P2=seq([
		recv(q, e_pid(p), id),
		recv(q, e_pid(p), id)
	       ]),
	T=(par([P1,  while(q, true, P2)])),
	Name=two-send-for-while.

rewrite_query(T, while(q, true, P2), _, Name) :-
	P1=for(P, _, x, send(P, e_pid(q), P)),
	P2=recv(q, e_pid(s), id),
	T=(par([sym(P,s, P1),  while(q, true, P2)])),
	Name=send-sym-for-while.

rewrite_query(T, while(q, true, P2), _, Name) :-
	P1=for(P, _, x,
	       seq([
		    send(P, e_pid(q), P),
		    recv(P, e_pid(q), val)
		   ])
	      ),
	P2=seq([recv(q, e_pid(s), id), send(q, e_var(id), ping)]),
	T=(par([sym(P,s, P1),  while(q, true, P2)])),
	Name=ping-sym-for-while.

rewrite_query(T, while(q, true, P2), _, Name) :-
	P1=for(P, _, x,
	       seq([
		    send(P, e_pid(q), P),
		    recv(P, e_pid(q), val),
		    send(P, e_pid(q), P),
		    recv(P, e_pid(q), val)
		   ])
	      ),
	P2=seq([recv(q, e_pid(s), id), send(q, e_var(id), ping)]),
	T=(par([sym(P,s, P1),  while(q, true, P2)])),
	Name=ping-twice-sym-for-while.

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

/*---------------------
Raft: leader election
---------------------*/

rewrite_query(T, skip, _, Name) :-
	/* followers */
	P1=
	seq([
	     assign(F, voted, 0),
	     for(F, _, c,
		 seq([
		      recv(F, e_pid(c), pair(id,term)),
		      if(F, term>cterm,
			 seq([
			      assign(F, cterm, term),
			      assign(F, voted, 0),
			      assign(F, votedFor, bottom)
			      ])
			),
		      ite(F,
			 (term>=cterm,implies(voted=1, votedFor=id)),
			 seq([
			      assign(F, voted, 1),
			      assign(F, votedFor, id),
			      assign(F, success, 1)
			     ]),
			  assign(F, success, 0)
			 ),
		      
		      send(F, e_var(id), success)
		     ])
		)
	    ]),
	/* Candidates */
	P2=seq([
		assign(C, count, 0),
		assign(C, isLeader, 0),
		for(C, F, f, send(C, e_pid(F), pair(C, cterm))),
		for(C, _, f,
		    seq([
			 recv(C, e_pid(f), success),
			 if(C, success, assign(C, count, count+1))
			])
		   ),
		if(C, 2*count>card(F), assign(C, isLeader, 1))
	       ]),
	T=(par([sym(F, f, P1), sym(C, c, P2)])),
	Name=raft-leader-election.

/*------
Conc DB
------*/

/*-----------
Encoding
-------------
alloc     : 0
get       : 1
------------*/

rewrite_query(T, while(db, true, DB), _, Name) :-
	Client=for(C, _, x,
	       seq([
		    send(C, e_pid(db), pair(C, pair(0, pair(x, v)))),
		    recv(C, e_pid(db), status),
		    send(C, e_pid(db), pair(C, pair(1, pair(x, v)))),
		    group(
			  recv(C, e_pid(db), vv),
			  pre(vv == v)
			 )
		   ])
	      ),
	DB=seq([
		recv(db, e_pid(c), pair(id, pair(req, pair(key, val)))),
		ite(db,
		    req=0,
		    ite(db, sel(domain,x)=1,
			assign(db,response,0),
			seq([ assign(db,response, pair(1,_)),
			      assign(db,domain,store(domain,key,1)),
			      assign(db,db,store(db,key,val))
			    ])
		       ),
		    ite(db,
			sel(domain,key)=1,
			seq([
			     assign(db, tag, 1),
			     assign(db,  v, sel(db,key)),
			     assign(db, response, pair(tag, v))
			    ]),
			seq([
			     assign(db, tag, 0),
			     assign(db,  v, 0),
			     assign(db, response, pair(tag, v))
			    ])
		       )
		   ),
		send(db, e_var(id), response)
	       ]),
	T=(par([
		sym(C, c, Client),
		while(db, true, DB)
	       ])
	  ),
	Name=concdb.