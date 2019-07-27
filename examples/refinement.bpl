var {:layer 0,2} x : int;

procedure {:atomic} {:layer 1,2} SET_X (v:int)
modifies x;
{ x := v; }

procedure {:atomic} {:layer 1,2} POS ()
modifies x;
{ var l:int; assume l > 0; x := l; }

procedure {:atomic} {:layer 1,2} STUPID_POS ()
modifies x;
{ var l:int; assume l >= 0; x := l+1; }

procedure {:yields} {:layer 0} {:refines "SET_X"} set_x (v:int);
procedure {:yields} {:layer 0} {:refines "POS"} pos ();

procedure {:yields} {:layer 1} {:refines "POS"} p ()
{
  yield;
  call set_x(1);
  yield;
}

procedure {:yields} {:layer 1} {:refines "STUPID_POS"} q ()
{
  yield;
  call set_x(1);
  yield;
}
