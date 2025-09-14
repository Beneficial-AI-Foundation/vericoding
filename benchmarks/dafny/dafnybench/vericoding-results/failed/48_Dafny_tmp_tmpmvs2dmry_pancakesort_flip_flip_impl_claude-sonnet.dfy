// flips (i.e., reverses) array elements in the range [0..num]

// <vc-helpers>

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
  var i := 0;
  while i <= num / 2
    invariant 0 <= i <= num / 2 + 1
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[num-k])
    invariant forall k :: 0 <= k < i ==> a[num-k] == old(a[k])
    invariant forall k :: num + 1 <= k < a.Length ==> a[k] == old(a[k])
    invariant forall k :: i <= k <= num - i ==> a[k] == old(a[k])
  {
    var temp := a[i];
    a[i] := a[num - i];
    a[num - i] := temp;
    i := i + 1;
  }
}
// </vc-code>

