// <vc-preamble>
function has_count(v: int, a: array<int>, n: int): int
    reads a
    requires n >= 0 && n <= a.Length
{
    if n == 0 then 0 else
    (if a[n-1] == v then has_count(v, a, n-1) + 1 else has_count(v, a, n-1))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed unnecessary lemma as Dafny can prove the invariant by unfolding */
// </vc-helpers>

// <vc-spec>
method count (v: int, a: array<int>, n: int) returns (r: int)
    requires n >= 0 && n <= a.Length;
    ensures has_count(v, a, n) == r;
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): removed call to helper lemma as it is unnecessary */
  r := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == has_count(v, a, i)
    decreases n - i
  {
    if a[i] == v {
      r := r + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
