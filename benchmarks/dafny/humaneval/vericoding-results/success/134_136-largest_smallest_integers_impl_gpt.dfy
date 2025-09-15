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
function min(a: int, b: int): int { if a < b then a else b }
function max(a: int, b: int): int { if a > b then a else b }
predicate AllNonNeg(s: seq<int>) { forall i :: 0 <= i < |s| ==> s[i] >= 0 }
predicate AllNonPos(s: seq<int>) { forall i :: 0 <= i < |s| ==> s[i] <= 0 }
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
  var hasNeg := false;
  var maxNeg := 0;
  var idxNeg := 0;
  var hasPos := false;
  var minPos := 0;
  var idxPos := 0;

  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant hasNeg ==> maxNeg < 0
    invariant hasNeg ==> 0 <= idxNeg < i && arr[idxNeg] == maxNeg
    invariant hasNeg ==> forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] <= maxNeg
    invariant !hasNeg ==> forall j :: 0 <= j < i ==> arr[j] >= 0
    invariant hasPos ==> minPos > 0
    invariant hasPos ==> 0 <= idxPos < i && arr[idxPos] == minPos
    invariant hasPos ==> forall j :: 0 <= j < i && arr[j] > 0 ==> arr[j] >= minPos
    invariant !hasPos ==> forall j :: 0 <= j < i ==> arr[j] <= 0
  {
    if arr[i] < 0 {
      if hasNeg {
        if maxNeg < arr[i] {
          maxNeg := arr[i];
          idxNeg := i;
        }
      } else {
        hasNeg := true;
        maxNeg := arr[i];
        idxNeg := i;
      }
    } else if arr[i] > 0 {
      if hasPos {
        if arr[i] < minPos {
          minPos := arr[i];
          idxPos := i;
        }
      } else {
        hasPos := true;
        minPos := arr[i];
        idxPos := i;
      }
    }
    i := i + 1;
  }

  if hasNeg {
    a := Some(maxNeg);
  } else {
    a := None;
  }

  if hasPos {
    b := Some(minPos);
  } else {
    b := None;
  }

  if hasNeg {
    assert 0 <= idxNeg < |arr| && arr[idxNeg] == maxNeg;
    assert maxNeg in arr;
    assert get_value(a) == maxNeg;
  }
  if hasPos {
    assert 0 <= idxPos < |arr| && arr[idxPos] == minPos;
    assert minPos in arr;
    assert get_value(b) == minPos;
  }
}
// </vc-code>
