function has_count(v: int, a: array<int>, n: int): int
    reads a  // This allows the function to read from array 'a'
    requires n >= 0 && n <= a.Length
{
    if n == 0 then 0 else
    (if a[n-1] == v then has_count(v, a, n-1) + 1 else has_count(v, a, n-1))
}

// <vc-helpers>
lemma lemma_has_count_iterative(v: int, a: array<int>, n: int)
  requires n >= 0 && n <= a.Length
  ensures has_count(v, a, n) ==
          (if n == 0 then 0 else
           (if a[n-1] == v then has_count(v, a, n-1) + 1 else has_count(v, a, n-1)))
{}

lemma lemma_has_count_iteration_properties(v: int, a: array<int>, i: int)
  requires i >= 0 && i < a.Length
  ensures has_count(v, a, i+1) == (if a[i] == v then has_count(v, a, i) + 1 else has_count(v, a, i))
{
  // This lemma directly proves the relationship needed for the loop invariant update.
  // It effectively unwraps has_count(v, a, i+1) using its definition.
}

// Additional lemma to help with the loop invariant.
// This lemma asserts that if has_count(v, a, i) is X, and a[i] == v, then has_count(v, a, i+1) is X+1.
// If has_count(v, a, i) is X, and a[i] != v, then has_count(v, a, i+1) is X.
lemma lemma_has_count_update(v: int, a: array<int>, i: int)
  requires 0 <= i < a.Length
  ensures (if a[i] == v then (has_count(v, a, i) + 1) else has_count(v, a, i)) == has_count(v, a, i+1)
{
  lemma_has_count_iteration_properties(v, a, i);
}
// </vc-helpers>

// <vc-spec>
method count (v: int, a: array<int>, n: int) returns (r: int)
    requires n >= 0 && n <= a.Length;
    ensures has_count(v, a, n) == r;
// </vc-spec>
// <vc-code>
{
  var r_local := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n;
    invariant r_local == has_count(v, a, i);
  {
    lemma_has_count_update(v, a, i);
    if a[i] == v {
      r_local := r_local + 1;
    }
    i := i + 1;
  }
  return r_local;
}
// </vc-code>

