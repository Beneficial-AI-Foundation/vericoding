// flips (i.e., reverses) array elements in the range [0..num]

// <vc-helpers>
lemma reversePreservesMultiset(a: array<int>, start: int, end: int)
  requires a != null
  requires 0 <= start <= end < a.Length
  ensures multiset(a[start..end+1]) == old(multiset(a[start..end+1]))
  decreases end - start
{
  if start < end {
    ghost var old_slice := a[start..end+1];
    ghost var temp_ghost := a[start];
    // Recursively prove for the inner range
    reversePreservesMultiset(a, start + 1, end - 1);
    ghost var new_slice := a[start..end+1];
    assert multiset(new_slice) == multiset(old_slice);
  }
}
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
  var j := num;
  while i < j
    invariant 0 <= i <= j + 1
    invariant j <= num
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[num-k])
    invariant forall k :: j < k <= num ==> a[k] == old(a[num-k])
    invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
    invariant forall k :: num < k < a.Length ==> a[k] == old(a[k])
    decreases j - i
  {
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
    i := i + 1;
    j := j - 1;
  }
}
// </vc-code>

