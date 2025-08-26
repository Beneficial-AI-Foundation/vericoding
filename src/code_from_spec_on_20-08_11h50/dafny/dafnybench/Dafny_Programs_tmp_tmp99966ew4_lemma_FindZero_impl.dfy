lemma SkippingLemma(a : array<int>, j : int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   requires 0 <= j < a.Length
   ensures forall k :: j <= k < j + a[j] && k < a.Length ==> a[k] != 0
{
   var i := j;
   while i < j + a[j] && i < a.Length
   decreases j + a[j] - i
      invariant i < a.Length ==> a[j] - (i-j) <= a[i]
      invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
   {
      i := i + 1;
   }
}

// <vc-helpers>
// </vc-helpers>

method FindZero(a: array<int>) returns (index: int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
   ensures 0 <= index ==> index < a.Length && a[index] == 0
// </vc-spec>
// <vc-code>
{
  if a.Length == 0 {
    return -1;
  }
  
  var j := 0;
  while j < a.Length
    invariant 0 <= j
    invariant forall k :: 0 <= k < j && k < a.Length ==> a[k] != 0
  {
    if a[j] == 0 {
      return j;
    } else {
      SkippingLemma(a, j);
      j := j + a[j];
    }
  }
  return -1;
}
// </vc-code>