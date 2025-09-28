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
  var largest_negative: Option<int> := None;
  var smallest_positive: Option<int> := None;
  
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant largest_negative.None? ==> forall j :: 0 <= j < i ==> arr[j] >= 0
    invariant largest_negative.Some? ==> get_value(largest_negative) in arr[0..i] && get_value(largest_negative) < 0
    invariant largest_negative.Some? ==> forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] <= get_value(largest_negative)
    invariant smallest_positive.None? ==> forall j :: 0 <= j < i ==> arr[j] <= 0
    invariant smallest_positive.Some? ==> get_value(smallest_positive) in arr[0..i] && get_value(smallest_positive) > 0
    invariant smallest_positive.Some? ==> forall j :: 0 <= j < i && arr[j] > 0 ==> arr[j] >= get_value(smallest_positive)
  {
    if arr[i] < 0 {
      if largest_negative.None? || arr[i] > get_value(largest_negative) {
        largest_negative := Some(arr[i]);
      }
    } else if arr[i] > 0 {
      if smallest_positive.None? || arr[i] < get_value(smallest_positive) {
        smallest_positive := Some(arr[i]);
      }
    }
    i := i + 1;
  }
  
  a := largest_negative;
  b := smallest_positive;
}
// </vc-code>
