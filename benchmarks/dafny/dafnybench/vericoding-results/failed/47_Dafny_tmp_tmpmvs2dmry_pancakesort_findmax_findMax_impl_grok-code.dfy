// returns an index of the largest element of array 'a' in the range [0..n)

// <vc-helpers>
method findMax (a: array<int>, n: int) returns (r: int)
  requires a.Length > 0
  requires 0 < n <= a.Length
  ensures 0 <= r < n <= a.Length
  ensures forall k :: 0 <= k < n <= a.Length ==> a[r] >= a[k]
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  r := 0;
  var i := 1;
  while i < n
    invariant 0 <= r < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j <= i ==> a[r] >= a[j]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if a[i] > a[r] {
      r := i;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method findMax (a : array<int>, n : int) returns (r:int)
requires a.Length > 0
requires 0 < n <= a.Length
ensures 0 <= r < n <= a.Length;
ensures forall k :: 0 <= k < n <= a.Length ==> a[r] >= a[k];
ensures multiset(a[..]) == multiset(old(a[..]));
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i := 1;
  while i < n
    invariant 0 <= r < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[r] >= a[j]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    if a[i] > a[r] {
      r := i;
    }
    i := i + 1;
  }
}
// </vc-code>

