datatype Option<T> = None | Some(value: T)
function get_value(o: Option<int>): int
  requires o.Some?
  ensures get_value(o) == o.value
{
  o.value
}

// <vc-helpers>
function get_largest_negative_in_seq(arr: seq<int>): Option<int>
  ensures (exists x :: x in arr && x < 0) ==> (get_largest_negative_in_seq(arr)).Some?
  ensures (forall x :: x in arr ==> x >= 0) ==> (get_largest_negative_in_seq(arr)).None?
  ensures forall x :: x in arr && x < 0 ==> x <= get_value(get_largest_negative_in_seq(arr))
  ensures (get_largest_negative_in_seq(arr)).Some? ==> get_value(get_largest_negative_in_seq(arr)) in arr
  ensures (get_largest_negative_in_seq(arr)).Some? ==> get_value(get_largest_negative_in_seq(arr)) < 0
{
  var largest_neg := None;
  for i := 0 to |arr| - 1
    invariant 0 <= i <= |arr|
    invariant largest_neg.None? ==> forall j :: 0 <= j < i ==> arr[j] >= 0
    invariant largest_neg.Some? ==> get_value(largest_neg) in arr[..i]
    invariant largest_neg.Some? ==> get_value(largest_neg) < 0
    invariant largest_neg.Some? ==> forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] <= get_value(largest_neg)
  {
    if arr[i] < 0 {
      if largest_neg.None? || arr[i] > get_value(largest_neg) {
        largest_neg := Some(arr[i]);
      }
    }
  }
  return largest_neg;
}

function get_smallest_positive_in_seq(arr: seq<int>): Option<int>
  ensures (exists x :: x in arr && x > 0) ==> (get_smallest_positive_in_seq(arr)).Some?
  ensures (forall x :: x in arr ==> x <= 0) ==> (get_smallest_positive_in_seq(arr)).None?
  ensures forall x :: x in arr && x > 0 ==> x >= get_value(get_smallest_positive_in_seq(arr))
  ensures (get_smallest_positive_in_seq(arr)).Some? ==> get_value(get_smallest_positive_in_seq(arr)) in arr
  ensures (get_smallest_positive_in_seq(arr)).Some? ==> get_value(get_smallest_positive_in_seq(arr)) > 0
{
  var smallest_pos := None;
  for i := 0 to |arr| - 1
    invariant 0 <= i <= |arr|
    invariant smallest_pos.None? ==> forall j :: 0 <= j < i ==> arr[j] <= 0
    invariant smallest_pos.Some? ==> get_value(smallest_pos) in arr[..i]
    invariant smallest_pos.Some? ==> get_value(smallest_pos) > 0
    invariant smallest_pos.Some? ==> forall j :: 0 <= j < i && arr[j] > 0 ==> arr[j] >= get_value(smallest_pos)
  {
    if arr[i] > 0 {
      if smallest_pos.None? || arr[i] < get_value(smallest_pos) {
        smallest_pos := Some(arr[i]);
      }
    }
  }
  return smallest_pos;
}
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
  var largest_neg_val := None;
  var smallest_pos_val := None;

  if |arr| == 0 {
    return largest_neg_val, smallest_pos_val;
  }

  largest_neg_val := get_largest_negative_in_seq(arr);
  smallest_pos_val := get_smallest_positive_in_seq(arr);
  
  return largest_neg_val, smallest_pos_val;
}
// </vc-code>

