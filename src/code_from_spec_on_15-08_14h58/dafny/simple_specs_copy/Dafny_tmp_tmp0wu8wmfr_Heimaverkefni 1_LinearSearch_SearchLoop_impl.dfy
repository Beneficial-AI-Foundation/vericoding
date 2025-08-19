//IMPL 
method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
  requires 0 <= i <= j <= |a|
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
  k := -1;
  var idx := i;
  
  while idx < j
    invariant i <= idx <= j
    invariant k == -1 || (i <= k < idx && a[k] == x)
    invariant k != -1 ==> forall r | k < r < idx :: a[r] != x
    invariant k == -1 ==> forall r | i <= r < idx :: a[r] != x
  {
    if a[idx] == x {
      k := idx;
    }
    idx := idx + 1;
  }
}