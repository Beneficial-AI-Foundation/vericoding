// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): replaced non-ghost Sum and lemma with a single ghost sum function */
ghost function sum(s: seq<int>): int
  decreases |s|
{
  if s == [] then 0 else s[0] + sum(s[1..])
}
// </vc-helpers>

// <vc-spec>
method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
    requires n > 0;
    requires n <= a.Length;
    requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
    ensures r <= max * n;
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): replaced recursive function call with an iterative while loop */
  r := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant r == sum(a[0..i])
    invariant r <= max * i
  {
    r := r + a[i];
    i := i + 1;
  }
}
// </vc-code>
