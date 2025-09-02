//ATOM


// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
  reads a
  requires a.Length1 == 2
{
  forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}


//IMPL Bubble Sort


// Bubble Sort
method bubble_sort(a: array2<int>)
  modifies a
  requires a.Length1 == 2
  ensures sorted(a, 0, a.Length0 - 1)
{
  var i := 0;
  while i < a.Length0
    invariant 0 <= i <= a.Length0
    invariant sorted(a, 0, i - 1)
    invariant forall k1, k2 :: 0 <= k1 < i <= k2 < a.Length0 ==> a[k1, 1] <= a[k2, 1]
  {
    var j := a.Length0 - 1;
    while j > i
      invariant i <= j < a.Length0
      invariant sorted(a, 0, i - 1)
      invariant forall k1, k2 :: 0 <= k1 < i <= k2 < a.Length0 ==> a[k1, 1] <= a[k2, 1]
      invariant forall k :: j < k < a.Length0 ==> a[j, 1] <= a[k, 1]
    {
      if a[j, 1] < a[j - 1, 1] {
        var temp0 := a[j, 0];
        var temp1 := a[j, 1];
        a[j, 0] := a[j - 1, 0];
        a[j, 1] := a[j - 1, 1];
        a[j - 1, 0] := temp0;
        a[j - 1, 1] := temp1;
      }
      j := j - 1;
    }
    i := i + 1;
  }
}