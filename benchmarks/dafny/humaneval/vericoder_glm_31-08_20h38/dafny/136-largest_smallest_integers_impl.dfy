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
  var hasNeg := false;
  var maxNeg := 0;
  var hasPos := false;
  var minPos := 0;

  for i := 0 to |arr|
    invariant !hasNeg ==> forall j: int | 0 <= j < i :: arr[j] >= 0
    invariant hasNeg ==> 
        maxNeg in arr[0..i] && 
        maxNeg < 0 && 
        (forall j: int | 0 <= j < i && arr[j] < 0 :: arr[j] <= maxNeg)
    invariant !hasPos ==> forall j: int | 0 <= j < i :: arr[j] <= 0
    invariant hasPos ==> 
        minPos in arr[0..i] && 
        minPos > 0 && 
        (forall j: int | 0 <= j < i && arr[j] > 0 :: arr[j] >= minPos)
  {
    var x := arr[i];
    if x < 0 {
      if !hasNeg {
        hasNeg := true;
        maxNeg := x;
      } else {
        if x > maxNeg {
          maxNeg := x;
        }
      }
    } else if x > 0 {
      if !hasPos {
        hasPos := true;
        minPos := x;
      } else {
        if x < minPos {
          minPos := x;
        }
      }
    }
  }

  a := if hasNeg then Some(maxNeg) else None;
  b := if hasPos then Some(minPos) else None;

  return;
}
// </vc-code>

