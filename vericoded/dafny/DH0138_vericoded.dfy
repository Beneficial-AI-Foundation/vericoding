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
  var max_neg := None;
  var min_pos := None;
  
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant max_neg.None? ==> forall j :: 0 <= j < i ==> arr[j] >= 0
    invariant max_neg.Some? ==> get_value(max_neg) in arr[0..i] && get_value(max_neg) < 0
    invariant max_neg.Some? ==> forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] <= get_value(max_neg)
    invariant min_pos.None? ==> forall j :: 0 <= j < i ==> arr[j] <= 0
    invariant min_pos.Some? ==> get_value(min_pos) in arr[0..i] && get_value(min_pos) > 0
    invariant min_pos.Some? ==> forall j :: 0 <= j < i && arr[j] > 0 ==> arr[j] >= get_value(min_pos)
  {
    if arr[i] < 0 {
      if max_neg.None? || arr[i] > get_value(max_neg) {
        max_neg := Some(arr[i]);
      }
    } else if arr[i] > 0 {
      if min_pos.None? || arr[i] < get_value(min_pos) {
        min_pos := Some(arr[i]);
      }
    }
    i := i + 1;
  }
  
  a := max_neg;
  b := min_pos;
}
// </vc-code>
