// <vc-preamble>
predicate StrictSorted(arr: array<int>)
    reads arr
{
    forall k, l :: 0 <= k < l < arr.Length ==> arr[k] < arr[l]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Mcontained(v: array<int>, w: array<int>, n: int, m: int) returns (b: bool)
    requires n <= m && n >= 0
    requires StrictSorted(v)
    requires StrictSorted(w)
    requires v.Length >= n && w.Length >= m
    ensures b ==> (forall k :: 0 <= k < n ==> (
        exists j :: 0 <= j < m && v[k] == w[j]
    ))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): improved loop invariants */
  var i := 0;
  var j := 0;
  while i < n && j < m
    invariant 0 <= i <= n
    invariant 0 <= j <= m
    invariant forall k :: 0 <= k < i ==> (exists l :: 0 <= l < j && v[k] == w[l])
    invariant i < n ==> forall l :: 0 <= l < j ==> w[l] < v[i]
    decreases n - i, m - j
  {
    if v[i] > w[j] {
      j := j + 1;
    } else if v[i] < w[j] {
      b := false;
      return;
    } else { // v[i] == w[j]
      i := i + 1;
      j := j + 1;
    }
  }
  b := (i == n);
}
// </vc-code>
