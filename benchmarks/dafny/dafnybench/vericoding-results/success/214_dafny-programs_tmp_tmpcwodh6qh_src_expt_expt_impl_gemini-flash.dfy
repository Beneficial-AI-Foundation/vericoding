ghost function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

// <vc-helpers>
lemma lemma_Expt_split(b: int, n: nat, k: nat)
  requires k <= n
  ensures Expt(b, n) == Expt(b, k) * Expt(b, n - k)
{
  if k == 0 {
    // Expt(b, n) == 1 * Expt(b, n) is trivially true
  } else if k == n {
    // Expt(b, n) == Expt(b, n) * 1 is trivially true
  } else {
    calc {
      Expt(b, n);
      b * Expt(b, n - 1);
      { lemma_Expt_split(b, n - 1, k - 1); }
      b * (Expt(b, k - 1) * Expt(b, n - 1 - (k - 1)));
      b * Expt(b, k - 1) * Expt(b, n - k);
      Expt(b, k) * Expt(b, n - k);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
// </vc-spec>
// <vc-code>
{
  var current_res := 1;
  var i := n;
  while i > 0
    invariant i >= 0
    invariant current_res * Expt(b, i) == Expt(b, n)
  {
    current_res := current_res * b;
    i := i - 1;
  }
  return current_res;
}
// </vc-code>

