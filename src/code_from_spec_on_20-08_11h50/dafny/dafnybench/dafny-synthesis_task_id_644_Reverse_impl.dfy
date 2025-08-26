method Reverse(a: array<int>)
    modifies a
    ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k])
// </vc-spec>
// <vc-code>
{
  if a.Length <= 1 {
    return;
  }
  
  var i := 0;
  var j := a.Length - 1;
  
  while i < j
    invariant 0 <= i <= j + 1 <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[(a.Length-1) - k])
    invariant forall k :: j < k < a.Length ==> a[k] == old(a[(a.Length-1) - k])
    invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
    invariant i + j == a.Length - 1
  {
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
    
    i := i + 1;
    j := j - 1;
  }
}
// </vc-code>
// <vc-helpers>
// </vc-helpers>