//IMPL
method IsSorted (a : array<int>) returns (isSorted : bool)
  ensures isSorted <==> forall j : int :: 1 <= j < a.Length ==> a[j-1] <= a[j]
{
  if a.Length <= 1 {
    return true;
  }
  
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall j : int :: 1 <= j < i ==> a[j-1] <= a[j]
  {
    if a[i-1] > a[i] {
      return false;
    }
    i := i + 1;
  }
  
  return true;
}