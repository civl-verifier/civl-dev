var {:layer 0,1} x : int;

// nondet is nonblocking, but the prover fails to show it. Ignore it!
// The point in this example is that the commutativity check between
// inc and nondet internally creates an existential quantifier because
// of the local variable l.

procedure {:left} {:layer 1} nondet ()
modifies x;
{
  var l:int;

  assume l >= 0;
  x := l;
}

procedure {:atomic} {:layer 1} inc ()
modifies x;
{
  if (*) { x := x + 1; }
} 
