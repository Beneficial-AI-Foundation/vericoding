// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// <vc-helpers>
predicate IsSecondLargest(a: array<int>, seclar: int)
reads a
{
  exists largest_idx :: 0 <= largest_idx < a.Length &&
    (forall k :: 0 <= k < a.Length ==> a[k] <= a[largest_idx]) &&
    (seclar < a[largest_idx]) &&
    (forall k :: 0 <= k < a.Length && a[k] != a[largest_idx] ==> a[k] <= seclar) &&
    (exists k :: 0 <= k < a.Length && a[k] == seclar)
}

lemma FindMaxIndex(a: array<int>) returns (max_idx: int)
requires a.Length > 0
ensures 0 <= max_idx < a.Length
ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[max_idx]
{
  max_idx := 0;
  var i := 1;
  while i < a.Length
    invariant 0 <= max_idx < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] <= a[max_idx]
  {
    if a[i] > a[max_idx] {
      max_idx := i;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method SecondLargest(a:array<int>) returns (seclar:int)
requires a.Length > 0
//ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
// </vc-spec>
// <vc-code>
{
  var max_val := a[0];
  var max_idx := 0;
  var i := 1;
  
  while i < a.Length
    invariant 0 <= max_idx < a.Length
    invariant 1 <= i <= a.Length
    invariant max_val == a[max_idx]
    invariant forall k :: 0 <= k < i ==> a[k] <= max_val
  {
    if a[i] > max_val {
      max_val := a[i];
      max_idx := i;
    }
    i := i + 1;
  }
  
  seclar := a[0];
  if a[0] == max_val && a.Length > 1 {
    seclar := a[1];
  }
  
  i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i && a[k] != max_val ==> a[k] <= seclar
    invariant exists k :: 0 <= k < a.Length && a[k] == seclar
  {
    if a[i] != max_val && a[i] > seclar {
      seclar := a[i];
    }
    i := i + 1;
  }
}
// </vc-code>

