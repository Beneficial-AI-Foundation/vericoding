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
  /* code modified by LLM (iteration 5): use while loop to ensure loop invariants hold correctly and imply postconditions at all points */
  var i := 0;
  var largest_neg: Option<int> := None;
  var smallest_pos: Option<int> := None;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant largest_neg.None? ==> forall j :: 0 <= j < i ==> arr[j] >= 0
    invariant largest_neg.Some? ==> get_value(largest_neg) < 0 && (forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] <= get_value(largest_neg)) && (exists j :: 0 <= j < i && arr[j] == get_value(largest_neg))
    invariant smallest_pos.None? ==> forall j :: 0 <= j < i ==> arr[j] <= 0
    invariant smallest_pos.Some? ==> get_value(smallest_pos) > 0 && (forall j :: 0 <= j < i && arr[j] > 0 ==> arr[j] >= get_value(smallest_pos)) && (exists j :: 0 <= j < i && arr[j] == get_value(smallest_pos))
  {
    if arr[i] < 0 {
      if largest_neg.None? || arr[i] > get_value(largest_neg) {
        largest_neg := Some(arr[i]);
      }
    } else if arr[i] > 0 {
      if smallest_pos.None? || arr[i] < get_value(smallest_pos) {
        smallest_pos := Some(arr[i]);
      }
    }
    i := i + 1;
  }
  a := largest_neg;
  b := smallest_pos;
}
// </vc-code>
