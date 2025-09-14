// <vc-preamble>
function sumTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else sumTo(a, n-1) + a[n-1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed sum comprehension syntax */
lemma sumTo_equiv_sum_expr(a: array<int>, n: int)
  requires 0 <= n <= a.Length
  ensures sumTo(a, n) == (sum i | 0 <= i < n :: a[i])
  decreases n
{
  if n > 0 {
    sumTo_equiv_sum_expr(a, n-1);
  }
}
// </vc-helpers>

// <vc-spec>
method ArraySum(a: array<int>) returns (result: int)
    ensures result == sumTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fixed sum comprehension syntax in loop invariant */
  result := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == (sum j | 0 <= j < i :: a[j])
    decreases a.Length - i
  {
    result := result + a[i];
    i := i + 1;
  }
  sumTo_equiv_sum_expr(a, a.Length);
}
// </vc-code>
