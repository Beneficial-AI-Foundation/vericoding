// flips (i.e., reverses) array elements in the range [0..num]

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method flip (a: array<int>, num: int)
requires a.Length > 0;
requires 0 <= num < a.Length;
modifies a;
ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k])
ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
// ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  var l := 0;
  var r := num;
  while l < r
    invariant 0 <= l <= num
    invariant 0 <= r <= num
    invariant num < a.Length
    invariant l + r == num
    invariant forall k :: 0 <= k < l ==> a[k] == old(a[num - k])
    invariant forall k :: r < k <= num ==> a[k] == old(a[num - k])
    invariant forall k :: l <= k <= r ==> a[k] == old(a[k])
    invariant forall k :: num < k < a.Length ==> a[k] == old(a[k])
    decreases r - l
  {
    var tmp := a[l];
    a[l] := a[r];
    a[r] := tmp;
    l := l + 1;
    r := r - 1;
  }
}
// </vc-code>

