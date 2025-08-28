// ex2

// this was me playing around to try and get an ensures for the method 
/*predicate method check(a: array<int>, seclar:int)
requires a.Length > 0
reads a
{ ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j]) } */

// <vc-helpers>
// Helper lemma to ensure properties of the second largest element
lemma SecondLargestExists(a: array<int>, maxVal: int, secondVal: int)
  requires a.Length > 0
  requires exists i :: 0 <= i < a.Length && a[i] == maxVal
  requires exists i :: 0 <= i < a.Length && a[i] == secondVal
  requires forall j :: 0 <= j < a.Length ==> a[j] <= maxVal
  requires secondVal <= maxVal
  requires forall j :: 0 <= j < a.Length && a[j] != maxVal ==> a[j] <= secondVal
  ensures exists i :: 0 <= i < a.Length && forall j :: 0 <= j < a.Length && j != i ==> a[i] >= a[j]
  ensures secondVal <= maxVal
  ensures forall j :: 0 <= j < a.Length && a[j] != maxVal ==> secondVal >= a[j]
{
  // The proof is implicit in the requires clauses matching the ensures conditions
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method SecondLargest(a:array<int>) returns (seclar:int)
requires a.Length > 0
//ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && ( if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
// </vc-spec>
// </vc-spec>

// <vc-code>
method SecondLargestImpl(a: array<int>) returns (seclar: int)
  requires a.Length > 0
  ensures exists i :: 0 <= i < a.Length && forall j :: (0 <= j < a.Length && j != i) ==> (a[i] >= a[j]) && (seclar <= a[i]) && (if a[j] != a[i] then seclar >= a[j] else seclar <= a[j])
{
  var maxVal := a[0];
  var secondVal := a[0];
  var i := 1;
  
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] <= maxVal
    invariant secondVal <= maxVal
    invariant forall k :: 0 <= k < i && a[k] != maxVal ==> a[k] <= secondVal
    invariant exists k :: 0 <= k < i && a[k] == maxVal
    invariant exists k :: 0 <= k < i && a[k] == secondVal
  {
    if a[i] > maxVal {
      secondVal := maxVal;
      maxVal := a[i];
    } else if a[i] > secondVal && a[i] < maxVal {
      secondVal := a[i];
    }
    i := i + 1;
  }
  
  seclar := secondVal;
  assert forall j :: 0 <= j < a.Length ==> a[j] <= maxVal;
  assert secondVal <= maxVal;
  assert forall j :: 0 <= j < a.Length && a[j] != maxVal ==> a[j] <= secondVal;
  assert exists i :: 0 <= i < a.Length && a[i] == maxVal;
  assert exists i :: 0 <= i < a.Length && a[i] == secondVal;
  // Invoke the lemma to bridge the gap between the assertions and the postcondition
  SecondLargestExists(a, maxVal, secondVal);
}
// </vc-code>
