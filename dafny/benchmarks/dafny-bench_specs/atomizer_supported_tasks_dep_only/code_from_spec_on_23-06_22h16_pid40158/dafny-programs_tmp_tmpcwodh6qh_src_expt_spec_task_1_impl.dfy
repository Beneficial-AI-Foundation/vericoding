// ATOM 
function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// IMPL 
method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
{
  if n == 0 {
    res := 1;
  } else {
    var temp := expt(b, n - 1);
    res := b * temp;
  }
}

// ATOM distributive
lemma distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)
{
  if a == 0 {
    // Base case: Expt(x, 0) * Expt(x, b) == 1 * Expt(x, b) == Expt(x, b) == Expt(x, 0 + b)
  } else {
    // Inductive case: use the recursive definition and the inductive hypothesis
    distributive(x, a - 1, b);
  }
}