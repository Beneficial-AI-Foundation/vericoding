// <vc-preamble>
datatype Option<T> = None | Some(value: T)
function get_value(o: Option<int>): int
  requires o.Some?
  ensures get_value(o) == o.value
{
  o.value
}
// </vc-preamble>

// <vc-helpers>
predicate IsLargestNegative(arr: seq<int>, v: int) { v in arr && v < 0 && (forall i :: 0 <= i < |arr| && arr[i] < 0 ==> arr[i] <= v) }

predicate IsSmallestPositive(arr: seq<int>, v: int) { v in arr && v > 0 && (forall i :: 0 <= i < |arr| && arr[i] > 0 ==> arr[i] >= v) }
// </vc-helpers>

// <vc-spec>
method largest_smallest_integers(arr: seq<int>) returns (a: Option<int>, b: Option<int>)

  ensures a.None? ==> forall i :: 0 <= i < |arr| ==> arr[i] >= 0
  ensures a.Some? ==> get_value(a) in arr && get_value(a) < 0
  ensures a.Some? ==> forall i :: 0 <= i < |arr| && arr[i] < 0 ==> arr[i] <= get_value(a)
  ensures b.None? ==> forall i :: 0 <= i < |arr| ==> arr[i] <= 0
  ensures b.Some? ==> get_value(b) in arr && get_value(b) > 0
  ensures b.Some? ==> forall i :: 0 <= i < |arr| && arr[i] > 0 ==> arr[i] >= get_value(b)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var negFound := false;
  var bestNeg := 0;
  var posFound := false;
  var bestPos := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant (!negFound) ==> (forall k :: 0 <= k < i ==> arr[k] >= 0)
    invariant negFound ==> bestNeg < 0
    invariant negFound ==> (exists k :: 0 <= k < i && arr[k] == bestNeg)
    invariant negFound ==> (forall k :: 0 <= k < i && arr[k] < 0 ==> arr[k] <= bestNeg)
    invariant (!posFound) ==> (forall k :: 0 <= k < i ==> arr[k] <= 0)
    invariant posFound ==> bestPos > 0
    invariant posFound ==> (exists k :: 0 <= k < i && arr[k] == bestPos)
    invariant posFound ==> (forall k :: 0 <= k < i && arr[k] > 0 ==> arr[k] >= bestPos)
  {
    if arr[i] < 0 {
      if negFound {
        if arr[i] > bestNeg {
          bestNeg := arr[i];
        }
      } else {
        negFound := true;
        bestNeg := arr[i];
      }
    }
    if arr[i] > 0 {
      if posFound {
        if arr[i] < bestPos {
          bestPos := arr[i];
        }
      } else {
        posFound := true;
        bestPos := arr[i];
      }
    }
    i := i + 1;
  }
  if negFound {
    a := Some(bestNeg);
  } else {
    a := None;
  }
  if posFound {
    b := Some(bestPos);
  } else {
    b := None;
  }
}
// </vc-code>
