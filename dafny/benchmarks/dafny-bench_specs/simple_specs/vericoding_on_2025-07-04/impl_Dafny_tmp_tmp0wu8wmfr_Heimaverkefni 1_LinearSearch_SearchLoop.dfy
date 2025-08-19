//IMPL
method SearchLoop( a: seq<int>, i: int, j: int, x: int ) returns (k: int)
  requires 0 <= i <= j <= |a|
  ensures i <= k < j || k == -1
  ensures k != -1 ==> a[k] == x
  ensures k != -1 ==> forall r | k < r < j :: a[r] != x
  ensures k == -1 ==> forall r | i <= r < j :: a[r] != x
{
  k := j - 1;
  while k >= i
    invariant k < j
    invariant forall r | k < r < j :: a[r] != x
    invariant k == -1 ==> forall r | i <= r < j :: a[r] != x
  {
    if a[k] == x {
      return;
    }
    k := k - 1;
  }
  k := -1;
}