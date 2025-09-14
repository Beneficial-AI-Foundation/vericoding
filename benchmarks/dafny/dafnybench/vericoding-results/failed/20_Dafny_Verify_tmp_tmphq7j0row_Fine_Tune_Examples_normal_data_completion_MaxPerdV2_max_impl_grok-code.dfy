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
function find_max(a: array<int>, n: int): int
  reads a
  requires 0 < n <= a.Length
  decreases n
{
  if n == 1 then a[0] else
    var m := find_max(a, n-1);
    if m > a[n-1] then m else a[n-1]
}
// </vc-helpers>

// <vc-spec>
method max(a: array<int>, n: int) returns (max: int)
  requires 0 < n <= a.Length;
  ensures is_max(max, a, n);
// </vc-spec>
// <vc-code>
{
  var res := a[0];
  var i := 1;
  while i < n
    invariant 0 < i <= n
    invariant forall k :: 0 <= k < i ==> a[k] <= res
    invariant exists k :: 0 <= k < i && a[k] == res
  {
    if res < a[i] {
      res := a[i];
    }
    i := i + 1;
  }
  max := res;
}
// </vc-code>

