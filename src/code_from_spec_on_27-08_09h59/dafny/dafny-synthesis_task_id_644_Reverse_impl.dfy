// <vc-helpers>
lemma SwapPreservesInvariants(a: array<int>, old_a: seq<int>, i: int, j: int)
    requires a.Length == |old_a|
    requires 0 <= i < j < a.Length
    requires forall k :: 0 <= k < i ==> a[k] == old_a[(a.Length-1) - k]
    requires forall k :: j < k < a.Length ==> a[k] == old_a[(a.Length-1) - k]
    requires forall k :: i <= k <= j ==> a[k] == old_a[k]
    modifies a
    ensures forall k :: 0 <= k < i+1 ==> a[k] == old_a[(a.Length-1) - k]
    ensures forall k :: j-1 < k < a.Length ==> a[k] == old_a[(a.Length-1) - k]
{
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method Reverse(a: array<int>)
    modifies a;
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var i := 0;
  var j := a.Length - 1;
  
  while i < j
    invariant 0 <= i <= j + 1 <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[(a.Length-1) - k])
    invariant forall k :: j < k < a.Length ==> a[k] == old(a[(a.Length-1) - k])
    invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
    decreases j - i
  {
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
    
    assert a[i] == old(a[j]) && a[j] == old(a[i]);
    assert old(a[j]) == old(a[(a.Length-1) - i]) && old(a[i]) == old(a[(a.Length-1) - j]);
    assert forall k :: 0 <= k < i ==> a[k] == old(a[(a.Length-1) - k]);
    assert forall k :: j+1 < k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
    
    i := i + 1;
    j := j - 1;
  }
}
// </vc-code>
