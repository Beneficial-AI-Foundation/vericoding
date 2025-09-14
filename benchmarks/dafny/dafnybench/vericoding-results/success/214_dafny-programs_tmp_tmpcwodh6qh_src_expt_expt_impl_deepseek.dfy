ghost function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// <vc-helpers>
lemma ExptLemma(b: int, n: nat)
  requires n >= 0
  ensures Expt(b, n) == (if n == 0 then 1 else b * Expt(b, n - 1))
{
  // This lemma helps Dafny understand the recursive definition
}
// </vc-helpers>

// <vc-spec>
method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
// </vc-spec>
// <vc-code>
{
  res := 1;
  var i := n;
  
  while i > 0
    invariant 0 <= i <= n
    invariant res * Expt(b, i) == Expt(b, n)
  {
    res := res * b;
    i := i - 1;
  }
}
// </vc-code>

