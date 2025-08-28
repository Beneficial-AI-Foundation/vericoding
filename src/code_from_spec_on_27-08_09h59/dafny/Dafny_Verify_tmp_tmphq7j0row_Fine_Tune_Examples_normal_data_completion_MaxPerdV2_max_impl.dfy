function contains(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  exists j :: 0 <= j < n && a[j] == v
}

function upper_bound(v: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  forall j :: 0 <= j < n ==> a[j] <= v
}

function is_max(m: int, a: array<int>, n: int): bool
reads a
  requires n <= a.Length
{
  contains(m, a, n) && upper_bound(m, a, n)
}

// <vc-helpers>
lemma max_properties(a: array<int>, n: int, max: int, max_idx: int)
  requires 0 < n <= a.Length
  requires 0 <= max_idx < n
  requires max == a[max_idx]
  requires forall k :: 0 <= k < n ==> a[k] <= max
  ensures is_max(max, a, n)
{
  assert contains(max, a, n) by {
    assert a[max_idx] == max;
  }
  assert upper_bound(max, a, n);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  max := a[0];
  var max_idx := 0;
  var i := 1;
  
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= max_idx < i
    invariant max == a[max_idx]
    invariant forall k :: 0 <= k < i ==> a[k] <= max
  {
    if a[i] > max {
      max := a[i];
      max_idx := i;
    }
    i := i + 1;
  }
  
  max_properties(a, n, max, max_idx);
}
// </vc-code>
