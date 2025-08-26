// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SecondLargest(a:array<int>) returns (seclar:int)
requires a.Length > 0
//ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
// </vc-spec>
// <vc-code>
{
  // Find the maximum element
  var max := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] <= max
    invariant exists k :: 0 <= k < i && a[k] == max
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
  
  // Find the second largest (largest element < max)
  var hasSecond := false;
  seclar := max; // default to max if no second largest exists
  i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant hasSecond ==> (seclar < max && forall k :: 0 <= k < i ==> (a[k] == max || a[k] <= seclar))
    invariant hasSecond ==> exists k :: 0 <= k < i && a[k] == seclar
    invariant !hasSecond ==> forall k :: 0 <= k < i ==> a[k] == max
  {
    if a[i] < max {
      if !hasSecond || a[i] > seclar {
        seclar := a[i];
        hasSecond := true;
      }
    }
    i := i + 1;
  }
}
// </vc-code>