datatype Option<T> = None | Some(value: T)
function get_value(o: Option<int>): int
  requires o.Some?
  ensures get_value(o) == o.value
{
  o.value
}

// <vc-helpers>
// No additional helpers needed for this verification.
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
method LargestSmallestIntegers(arr: seq<int>) returns (a: Option<int>, b: Option<int>)
{
  var smallest_neg: Option<int> := None;
  var largest_pos: Option<int> := None;
  
  for i := 0 to |arr|
    invariant smallest_neg.None? ==> forall k :: 0 <= k < i ==> arr[k] >= 0
    invariant smallest_neg.Some? ==> get_value(smallest_neg) in arr[..i] && get_value(smallest_neg) < 0
    invariant smallest_neg.Some? ==> forall k :: 0 <= k < i && arr[k] < 0 ==> arr[k] <= get_value(smallest_neg)
    invariant largest_pos.None? ==> forall k :: 0 <= k < i ==> arr[k] <= 0
    invariant largest_pos.Some? ==> get_value(largest_pos) in arr[..i] && get_value(largest_pos) > 0
    invariant largest_pos.Some? ==> forall k :: 0 <= k < i && arr[k] > 0 ==> arr[k] >= get_value(largest_pos)
  {
    if arr[i] < 0 {
      if smallest_neg.None? || arr[i] > get_value(smallest_neg) {
        smallest_neg := Some(arr[i]);
      }
    } else if arr[i] > 0 {
      if largest_pos.None? || arr[i] < get_value(largest_pos) {
        largest_pos := Some(arr[i]);
      }
    }
  }
  
  return smallest_neg, largest_pos;
}
// </vc-code>
