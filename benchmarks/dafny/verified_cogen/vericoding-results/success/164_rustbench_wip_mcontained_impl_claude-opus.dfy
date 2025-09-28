// <vc-preamble>
predicate StrictSorted(arr: array<int>)
    reads arr
{
    forall k, l :: 0 <= k < l < arr.Length ==> arr[k] < arr[l]
}
// </vc-preamble>

// <vc-helpers>
predicate AllContained(v: array<int>, w: array<int>, n: int, m: int, i: int)
  requires 0 <= i <= n <= v.Length
  requires 0 <= m <= w.Length
  reads v, w
{
  forall k :: 0 <= k < i ==> exists j :: 0 <= j < m && v[k] == w[j]
}

/* helper modified by LLM (iteration 4): Binary search method to find element in sorted array */
method BinarySearchExists(w: array<int>, m: int, target: int) returns (found: bool, index: int)
  requires 0 <= m <= w.Length
  requires StrictSorted(w)
  ensures found ==> 0 <= index < m && w[index] == target
  ensures !found ==> forall j :: 0 <= j < m ==> w[j] != target
{
  var lo, hi := 0, m;
  while lo < hi
    invariant 0 <= lo <= hi <= m
    invariant forall j :: 0 <= j < lo ==> w[j] < target
    invariant forall j :: hi <= j < m ==> w[j] > target
  {
    var mid := lo + (hi - lo) / 2;
    if w[mid] < target {
      lo := mid + 1;
    } else if w[mid] > target {
      hi := mid;
    } else {
      found := true;
      index := mid;
      return;
    }
  }
  found := false;
  index := 0;
}
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
  /* code modified by LLM (iteration 4): Check all elements of v are contained in w */
  var i := 0;
  b := true;
  
  while i < n
    invariant 0 <= i <= n
    invariant b ==> forall k :: 0 <= k < i ==> exists j :: 0 <= j < m && v[k] == w[j]
  {
    var found, index := BinarySearchExists(w, m, v[i]);
    if !found {
      b := false;
      return;
    }
    i := i + 1;
  }
  
  if !b {
    return;
  }
  
  assert i == n;
  assert b ==> forall k :: 0 <= k < n ==> exists j :: 0 <= j < m && v[k] == w[j];
}
// </vc-code>
