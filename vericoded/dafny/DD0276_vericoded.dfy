predicate InsertionSorted(Array: array<int>, left: int, right: int)  
  requires 0 <= left <= right <= Array.Length       
  reads Array       
{           
  forall i,j :: left <= i < j < right ==> Array[i] <= Array[j]
}

// <vc-helpers>
// No helper methods required for this verification.
// </vc-helpers>

// <vc-spec>
method sorting(Array: array<int>)
  requires Array.Length > 1 
  ensures InsertionSorted(Array, 0, Array.Length) 
  modifies Array
// </vc-spec>
// <vc-code>
{
  var n := Array.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant InsertionSorted(Array, 0, i)
    invariant forall p, q :: 0 <= p < i && i <= q < n ==> Array[p] <= Array[q]
    decreases n - i
  {
    var idx := i;
    var j := i + 1;
    while j < n
      invariant i <= idx < n
      invariant i + 1 <= j <= n
      invariant forall k :: i <= k < j ==> Array[idx] <= Array[k]
      decreases n - j
    {
      if Array[j] < Array[idx] {
        idx := j;
      }
      j := j + 1;
    }
    // swap Array[i] and Array[idx]
    var tmp := Array[i];
    Array[i] := Array[idx];
    Array[idx] := tmp;
    i := i + 1;
  }
}
// </vc-code>

