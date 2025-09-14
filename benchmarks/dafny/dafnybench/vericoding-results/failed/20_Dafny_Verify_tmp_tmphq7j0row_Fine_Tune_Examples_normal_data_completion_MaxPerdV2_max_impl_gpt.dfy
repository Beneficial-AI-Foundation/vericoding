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
lemma Contains_from_witness(v: int, a: array<int>, n: int, j: int)
  requires n <= a.Length
  requires 0 <= j < n
  requires a[j] == v
  ensures contains(v, a, n)
{
  assert exists k :: 0 <= k < n && a[k] == v;
}
// </vc-helpers>

// <vc-spec>
method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
// </vc-spec>
// <vc-code>
{
  var idx := 0;
  max := a[0];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant i <= a.Length
    invariant 0 <= idx < i
    invariant a[idx] == max
    invariant forall j :: 0 <= j < i ==> a[j] <= max
    decreases n - i
  {
    if a[i] > max {
      max := a[i];
      idx := i;
    }
    i := i + 1;
  }
  Contains_from_witness(max, a, n, idx);
}
// </vc-code>

