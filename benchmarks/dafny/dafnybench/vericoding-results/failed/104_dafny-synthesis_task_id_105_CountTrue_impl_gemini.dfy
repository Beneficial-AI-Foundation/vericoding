// <vc-preamble>
function countTo( a:array<bool>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  decreases n;
  reads a;
{
  if (n == 0) then 0 else countTo(a, n-1) + (if a[n-1] then 1 else 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed syntax error in sum comprehension */
lemma CountToSum(a: array<bool>, n: int)
  requires a != null
  requires 0 <= n <= a.Length
  ensures countTo(a, n) == sum i: int | 0 <= i < n :: if a[i] then 1 else 0
  decreases n
{
  if n > 0 {
    CountToSum(a, n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
method CountTrue(a: array<bool>) returns (result: int)
    requires a != null
    ensures result == countTo(a, a.Length)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed syntax error in loop invariant */
  result := 0;
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant result == sum j: int | 0 <= j < i :: if a[j] then 1 else 0
  {
    if a[i] {
      result := result + 1;
    }
    i := i + 1;
  }
  CountToSum(a, a.Length);
}
// </vc-code>
