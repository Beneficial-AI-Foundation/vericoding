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
  var i: int := 0;
  var curNeg: Option<int> := None;
  var jNeg: int := -1;
  var curPos: Option<int> := None;
  var jPos: int := -1;

  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant curNeg.None? ==> (forall k :: 0 <= k < i ==> arr[k] >= 0)
    invariant (forall k :: 0 <= k < i && arr[k] < 0 ==> curNeg.Some?)
    invariant curNeg.Some? ==> (forall k :: 0 <= k < i && arr[k] < 0 ==> arr[k] <= get_value(curNeg))
    invariant curNeg.Some? ==> get_value(curNeg) < 0
    invariant curNeg.Some? ==> 0 <= jNeg < i && arr[jNeg] == get_value(curNeg)
    invariant curPos.None? ==> (forall k :: 0 <= k < i ==> arr[k] <= 0)
    invariant (forall k :: 0 <= k < i && arr[k] > 0 ==> curPos.Some?)
    invariant curPos.Some? ==> (forall k :: 0 <= k < i && arr[k] > 0 ==> arr[k] >= get_value(curPos))
    invariant curPos.Some? ==> get_value(curPos) > 0
    invariant curPos.Some? ==> 0 <= jPos < i && arr[jPos] == get_value(curPos)
    decreases |arr| - i
  {
    var x := arr[i];
    if x < 0 {
      if curNeg.Some? {
        if get_value(curNeg) < x {
          curNeg := Some(x);
          jNeg := i;
        }
      } else {
        curNeg := Some(x);
        jNeg := i;
      }
    } else if x > 0 {
      if curPos.Some? {
        if x < get_value(curPos) {
          curPos := Some(x);
          jPos := i;
        }
      } else {
        curPos := Some(x);
        jPos := i;
      }
    }
    i := i + 1;
  }

  // Helpful assertions for membership
  if curNeg.Some? {
    assert 0 <= jNeg < |arr|;
    assert arr[jNeg] in arr;
  }
  if curPos.Some? {
    assert 0 <= jPos < |arr|;
    assert arr[jPos] in arr;
  }

  a := curNeg;
  b := curPos;
}
// </vc-code>

