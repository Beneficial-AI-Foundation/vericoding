

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var j := a.Length - 1;
  
  while i < j
    invariant 0 <= i <= a.Length / 2
    invariant j == a.Length - 1 - i
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: j < k < a.Length ==> a[k] == old(a[a.Length - 1 - k])
    invariant forall k :: i <= k <= j ==> a[k] == old(a[k])
  {
    var temp := a[i];
    a[i] := a[j];
    a[j] := temp;
    i := i + 1;
    j := j - 1;
  }
}
// </vc-code>

