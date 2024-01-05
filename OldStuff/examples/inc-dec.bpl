var x:int;

procedure {:inline 1} INC()
modifies x;
{
  if (*)
  {
    x := x + 1;
  }
}

procedure {:inline 1} DEC()
modifies x;
{
  if (*)
  {
    x := x - 1;
  }
}

// witness function
function {:witness "x INC DEC"} f (x:int, x':int) : int
{
  if x' >= x then x else x - 1
}

function {:witness "x INC DEC"} g (x:int, x':int) : int
{
  x
}

function {:witness "x INC DEC"} h (x:int, x':int) : int
{
  x - 1
}

// In this procedure the effect of INC ∘ DEC is created by calling them in sequence
procedure CommutativityChecker_INC_DEC()
modifies x;
{
  call INC();
  call DEC();

  // The transition relation of DEC ∘ INC computed by the current implementation
  assert
    x == old(x) - 1 + 1 ||
    x == old(x) - 1 ||
    x == old(x) + 1 ||
    x == old(x);

  // The transition relation of DEC ∘ INC with explicit quantifier
  assert (exists x':int :: (x' == old(x) || x' == old(x) - 1) && (x == x' || x == x' + 1));

  // Unfolding the existential quantifier to a disjunction with x' ↦ old(x) and x' ↦ old(x)-1
  assert ((old(x) == old(x) || old(x) == old(x) - 1) && (x == old(x) || x == old(x) + 1)) ||
         ((old(x)-1 == old(x) || old(x)-1 == old(x) - 1) && (x == old(x)-1 || x == old(x)-1 + 1));

  // Skolemizing the existential quantifier with a witness function f that has access to the pre and post state
  // Definition of is is given above
  assert (f(old(x),x) == old(x) || f(old(x),x) == old(x) - 1) && (x == f(old(x),x) || x == f(old(x),x) + 1);

  // Supplying two different witness functions g and h
  assert ((g(old(x),x) == old(x) || g(old(x),x) == old(x) - 1) && (x == g(old(x),x) || x == g(old(x),x) + 1)) ||
         ((h(old(x),x) == old(x) || h(old(x),x) == old(x) - 1) && (x == h(old(x),x) || x == h(old(x),x) + 1));
}

// In this procedure the effect of INC ∘ DEC is created by joining together their transition relations
procedure CommutativityChecker_INC_DEC_2 ()
modifies x;
{
  var xx:int;
  havoc xx;
  // Transition relation of INC ∘ DEC
  assume (xx == old(x) || xx == old(x) + 1) && (x == xx || x == xx - 1);

  // Strangely, when the definitions of tr and f are removed then this assertion (and the same one above) verifies
  assert (exists x':int :: (x' == old(x) || x' == old(x) - 1) && (x == x' || x == x' + 1));
}
