//ATOM
function C(n: nat): nat 
{
  if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}

//IMPL
/* code modified by LLM (iteration 1): Added helper lemma and enhanced loop invariants to resolve timeout */
lemma CatalanRecursion(i: nat)
  requires i > 0
  ensures C(i) == (4 * i - 2) * C(i - 1) / (i + 1)
{
  // This follows directly from the definition of C
}

method calcC(n: nat) returns (res: nat)
  ensures res == C(n)
{
  if n == 0 {
    res := 1;
  } else {
    res := 1;
    var i := 1;
    while i <= n
      invariant 1 <= i <= n + 1
      invariant res == C(i - 1)
      /* code modified by LLM (iteration 1): Added decreases clause to help with termination */
      decreases n - i + 1
    {
      /* code modified by LLM (iteration 1): Added assertion to help Dafny prove the invariant */
      assert res == C(i - 1);
      CatalanRecursion(i);
      assert C(i) == (4 * i - 2) * C(i - 1) / (i + 1);
      res := (4 * i - 2) * res / (i + 1);
      /* code modified by LLM (iteration 1): Added assertion to help maintain invariant */
      assert res == C(i);
      i := i + 1;
    }
  }
}