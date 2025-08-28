// flips (i.e., reverses) array elements in the range [0..num]

// <vc-helpers>
lemma FlipInvariant(a: array<int>, i: int, num: int, oldA: seq<int>)
  requires a.Length > 0
  requires 0 <= num < a.Length
  requires 0 <= i <= (num + 1) / 2
  requires forall k :: 0 <= k < i ==> a[k] == oldA[num - k]
  requires forall k :: 0 <= k < i ==> a[num - k] == oldA[k]
  requires forall k :: i <= k <= num - i ==> a[k] == oldA[k]
  requires forall k :: num < k < a.Length ==> a[k] == oldA[k]
  ensures forall k :: 0 <= k <= num ==> a[k] == oldA[num - k] || (i <= k <= num - i)
  ensures forall k :: num < k < a.Length ==> a[k] == oldA[k]
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method flip (a: array<int>, num: int)
requires a.Length > 0;
requires 0 <= num < a.Length;
modifies a;
ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k])
ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
// ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// </vc-spec>

// <vc-code>
method Flip(a: array<int>, num: int)
  requires a.Length > 0
  requires 0 <= num < a.Length
  modifies a
  ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num - k])
  ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
{
  var i := 0;
  while i < (num + 1) / 2
    invariant 0 <= i <= (num + 1) / 2
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[num - k])
    invariant forall k :: 0 <= k < i ==> a[num - k] == old(a[k])
    invariant forall k :: i <= k <= num - i ==> a[k] == old(a[k])
    invariant forall k :: num < k < a.Length ==> a[k] == old(a[k])
  {
    var temp := a[i];
    a[i] := a[num - i];
    a[num - i] := temp;
    i := i + 1;
  }
}
// </vc-code>
