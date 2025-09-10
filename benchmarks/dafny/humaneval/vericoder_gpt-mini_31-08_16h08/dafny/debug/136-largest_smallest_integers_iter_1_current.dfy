datatype Option<T> = None | Some(value: T)
function get_value(o: Option<int>): int
  requires o.Some?
  ensures get_value(o) == o.value
{
  o.value
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method largest_smallest_integers(arr: seq<int>) returns (a: Option<int>, b: Option<int>)
  // post-conditions-start
  ensures a.None? ==> forall i :: 0 <= i < |arr| ==> arr[i] >= 0
  ensures a.Some? ==> get_value(a) in arr && get_value(a) < 0
  ensures a.Some? ==> forall i :: 0 <= i < |arr| && arr[i] < 0 ==> arr[i] <= get_value(a)
  ensures b.None? ==> forall i :: 0 <= i < |arr| ==> arr[i] <= 0
  ensures b.Some? ==> get_value(b) in arr && get_value(b) > 0
  ensures b.Some? ==> forall i :: 0 <= i < |arr| && arr[i] > 0 ==> arr[i] >= get_value(b)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  var foundNeg := false;
  var maxNeg := 0;
  var maxNegIdx := 0;
  var foundPos := false;
  var minPos := 0;
  var minPosIdx := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant foundNeg == (exists k :: 0 <= k < i && arr[k] < 0)
    invariant foundNeg ==> 0 <= maxNegIdx < i
    invariant foundNeg ==> maxNeg == arr[maxNegIdx] && arr[maxNegIdx] < 0
    invariant foundNeg ==> forall k :: 0 <= k < i && arr[k] < 0 ==> arr[k] <= maxNeg
    invariant foundPos == (exists k :: 0 <= k < i && arr[k] > 0)
    invariant foundPos ==> 0 <= minPosIdx < i
    invariant foundPos ==> minPos == arr[minPosIdx] && arr[minPosIdx] > 0
    invariant foundPos ==> forall k :: 0 <= k < i && arr[k] > 0 ==> arr[k] >= minPos
  {
    var x := arr[i];
    if x < 0 {
      if !foundNeg {
        foundNeg := true;
        maxNeg := x;
        maxNegIdx := i;
      } else if x > maxNeg {
        maxNeg := x;
        maxNegIdx := i;
      }
    }
    if x > 0 {
      if !foundPos {
        foundPos := true;
        minPos := x;
        minPosIdx := i;
      } else if x < minPos {
        minPos := x;
        minPosIdx := i;
      }
    }
    i := i + 1;
  }
  if foundNeg {
    a := Some(maxNeg);
  } else {
    a := None;
  }
  if foundPos {
    b := Some(minPos);
  } else {
    b := None;
  }
}
// </vc-code>

