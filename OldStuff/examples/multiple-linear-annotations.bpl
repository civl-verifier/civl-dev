type pid = int;

var {:layer 0,1} x:int;
var {:layer 0,1} y:int;

// Currently, CIVL only recognizes ps to be linear in domain X, but not in domain Y.
procedure {:atomic}{:layer 1} MAIN ({:linear_in "X"}{:linear_in "Y"} ps:[pid]bool)
modifies x, y;
{
  assert ps == (lambda i:pid :: true);
  x := 0;
  y := 0;
}

procedure {:left}{:layer 1} X ({:linear_in "X"} i:pid)
modifies x;
{
  x := 1;
}

procedure {:left}{:layer 1} Y ({:linear_in "Y"} i:pid)
modifies y;
{
  y := 2;
}

function {:builtin "MapConst"} MapConstBool(bool) : [pid]bool;
function {:inline}{:linear "X"} XCollector(i:pid) : [pid]bool
{
  MapConstBool(false)[i := true]
}
function {:inline}{:linear "Y"} YCollector(i:pid) : [pid]bool
{
  MapConstBool(false)[i := true]
}
function {:inline}{:linear "X"} XSetCollector(ps:[pid]bool) : [pid]bool
{
  ps
}
function {:inline}{:linear "Y"} YSetCollector(ps:[pid]bool) : [pid]bool
{
  ps
}
