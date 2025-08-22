///////////////////
// Binary search
///////////////////

//ATOM 
predicate isSorted(a:array<int>)
  reads a
{
  forall i, j :: 0 <= i <= j < a.Length ==> a[i] <= a[j]
}

//IMPL binSearch
method binSearch(a:array<int>, K:int) returns (b:bool)
  requires isSorted(a)
  ensures b == exists i:nat :: i < a.Length && a[i] == K
{
  if a.Length == 0 {
    b := false;
    return;
  }
  
  var lo := 0;
  var hi := a.Length;
  
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall i :: 0 <= i < lo ==> a[i] < K
    invariant forall i :: hi <= i < a.Length ==> a[i] > K
  {
    var mid := (lo + hi) / 2;
    
    if a[mid] == K {
      b := true;
      return;
    } else if a[mid] < K {
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  
  b := false;
}