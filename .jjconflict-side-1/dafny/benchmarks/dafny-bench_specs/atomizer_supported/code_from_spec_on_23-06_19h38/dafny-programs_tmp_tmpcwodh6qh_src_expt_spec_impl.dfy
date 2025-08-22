// ATOM 
function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// IMPL expt
method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
{
  res := 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant res == Expt(b, i)
  {
    res := res * b;
    i := i + 1;
  }
}

// IMPL distributive
lemma distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)
{
  if a == 0 {
    // Base case: Expt(x, 0) * Expt(x, b) == 1 * Expt(x, b) == Expt(x, b) == Expt(x, 0 + b)
  } else {
    // Inductive case: use the recursive definition and inductive hypothesis
    distributive(x, a - 1, b);
    // Now we have: Expt(x, a-1) * Expt(x, b) == Expt(x, (a-1) + b)
    // We need to show: Expt(x, a) * Expt(x, b) == Expt(x, a + b)
    // Expt(x, a) = x * Expt(x, a-1) by definition
    // So: Expt(x, a) * Expt(x, b) = x * Expt(x, a-1) * Expt(x, b)
    //                              = x * (Expt(x, a-1) * Expt(x, b))
    //                              = x * Expt(x, (a-1) + b)    [by IH]
    //                              = x * Expt(x, a + b - 1)
    //                              = Expt(x, a + b)            [by definition]
  }
}