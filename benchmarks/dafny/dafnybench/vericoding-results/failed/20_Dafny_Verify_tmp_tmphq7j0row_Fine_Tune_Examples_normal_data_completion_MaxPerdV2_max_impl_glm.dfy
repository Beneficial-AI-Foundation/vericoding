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
lemma lemma_upper_bound_extension_by_element(m: int, a: array<int>, i: int)
  requires 0 <= i < a.Length
  requires upper_bound(m, a, i)
  requires a[i] > m
  ensures upper_bound(a[i], a, i+1);
{
  forall j | 0 <= j < i+1
    ensures a[j] <= a[i]
  {
    if j < i {
      assert a[j] <= m;
      assert m < a[i];
    } else {
      assert j == i;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
// </vc-spec>
// <vc-code>
{
  max := a[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant is_max(max, a, i)
  {
    if a[i] > max {
      lemma_upper_bound_extension_by_element(max, a, i);
      max := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>

