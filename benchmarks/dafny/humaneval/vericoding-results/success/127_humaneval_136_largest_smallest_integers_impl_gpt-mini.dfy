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
function isNeg(x: int): bool { x < 0 }
function isPos(x: int): bool { x > 0 }
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
  var neg: Option<int> := None;
  var pos: Option<int> := None;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant (neg.None? ==> forall j :: 0 <= j < i ==> arr[j] >= 0)
    invariant (neg.Some? ==> get_value(neg) in arr[..i])
    invariant (neg.Some? ==> get_value(neg) < 0)
    invariant (neg.Some? ==> forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] <= get_value(neg))
    invariant (pos.None? ==> forall j :: 0 <= j < i ==> arr[j] <= 0)
    invariant (pos.Some? ==> get_value(pos) in arr[..i])
    invariant (pos.Some? ==> get_value(pos) > 0)
    invariant (pos.Some? ==> forall j :: 0 <= j < i && arr[j] > 0 ==> arr[j] >= get_value(pos))
  {
    var v := arr[i];
    if v < 0 {
      if neg.None? {
        neg := Some(v);
      } else {
        if v > get_value(neg) {
          neg := Some(v);
        }
      }
    }
    if v > 0 {
      if pos.None? {
        pos := Some(v);
      } else {
        if v < get_value(pos) {
          pos := Some(v);
        }
      }
    }
    i := i + 1;
  }
  a := neg;
  b := pos;
}
// </vc-code>
