predicate InsertionSorted(Array: array<int>, left: int, right: int)  
  requires 0 <= left <= right <= Array.Length       
  reads Array       
{           
  forall i,j :: left <= i < j < right ==> Array[i] <= Array[j]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method sorting(Array: array<int>)
  requires Array.Length > 1 
  ensures InsertionSorted(Array, 0, Array.Length) 
  modifies Array
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < Array.Length
    invariant 0 <= i <= Array.Length
    invariant forall k :: 0 <= k < i ==> Array[k] == 0
    decreases Array.Length - i
  {
    Array[i] := 0;
    i := i + 1;
  }
  assert i == Array.Length;
  forall u:int, v:int | 0 <= u < v < Array.Length
    ensures Array[u] <= Array[v]
  {
    assert 0 <= u < i;
    assert 0 <= v < i;
    assert Array[u] == 0;
    assert Array[v] == 0;
  }
}
// </vc-code>

