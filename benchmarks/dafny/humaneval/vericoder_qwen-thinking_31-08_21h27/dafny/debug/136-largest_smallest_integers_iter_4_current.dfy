datatype Option<T> = None | Some(value: T)
function get_value(o: Option<int>): int
  requires o.Some?
  ensures get_value(o) == o.value
{
  o.value
}

// <vc-helpers>
datatype Option<T> = None | Some(value: T)
function get_value(o: Option<int>): int
  requires o.Some?
  ensures get_value(o) == o.value
{
  o.value
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
var current_a: Option<int> := None<int>;
var current_b: Option<int> := None<int>;
for i := 0 to |arr| - 1 {
    invariant (current_a.None? || (get_value(current_a) in arr[..i] && (forall k :: 0 <= k < i && arr[k] < 0 ==> arr[k] <= get_value(current_a))))
    invariant (current_b.None? || (get_value(current_b) in arr[..i] && (forall k :: 0 <= k < i && arr[k] > 0 ==> get_value(current_b) <= arr[k])))
    if arr[i] < 0 {
        if current_a.None? {
            current_a := Some(arr[i]);
        } else {
            if arr[i] > get_value(current_a) {
                current_a := Some(arr[i]);
            }
        }
    }
    if arr[i] > 0 {
        if current_b.None? {
            current_b := Some(arr[i]);
        } else {
            if arr[i] < get_value(current_b) {
                current_b := Some(arr[i]);
            }
        }
    }
}
a := current_a;
b := current_b;
// </vc-code>

