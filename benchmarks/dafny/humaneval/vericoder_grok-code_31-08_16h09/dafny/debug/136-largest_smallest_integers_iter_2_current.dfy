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
  a := None;
  b := None;
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant a.None? ==> forall j :: 0 <= j < i ==> arr[j] >= 0
    invariant a.Some? ==> forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] <= get_value(a)
    invariant a.Some? ==> exists j :: 0 <= j < i && arr[j] == get_value(a)
    invariant a.Some? ==> get_value(a) < 0
    invariant b.None? ==> forall j :: 0 <= j < i ==> arr[j] <= 0
    invariant b.Some? ==> forall j :: 0 <= j < i && arr[j] > 0 ==> arr[j] >= get_value(b)
    invariant b.Some? ==> exists j :: 0 <= j < i && arr[j] == get_value(b)
    invariant b.Some? ==> get_value(b) > 0
  {
    if arr[i] < 0 {
      if a.None? || (a.Some? && arr[i] > get_value(a)) {
        a := Some(arr[i]);
      }
    } else if arr[i] > 0 {
      if b.None? || (b.Some? && arr[i] < get_value(b)) {
        b := Some(arr[i]);
      }
    }
    i := i + 1;
  }
}
// </vc-code>

