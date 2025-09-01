datatype Option<T> = None | Some(value: T)
function get_value(o: Option<int>): int
  requires o.Some?
  ensures get_value(o) == o.value
{
  o.value
}

// <vc-helpers>
predicate is_largest_negative(arr: seq<int>, candidate: int) {
  candidate in arr && candidate < 0 &&
  (forall i :: 0 <= i < |arr| && arr[i] < 0 ==> arr[i] <= candidate)
}

predicate is_smallest_positive(arr: seq<int>, candidate: int) {
  candidate in arr && candidate > 0 &&
  (forall i :: 0 <= i < |arr| && arr[i] > 0 ==> arr[i] >= candidate)
}

lemma largest_negative_properties(arr: seq<int>)
  ensures (exists x :: x in arr && x < 0) ==> 
          (exists x :: is_largest_negative(arr, x))
{
  if exists x :: x in arr && x < 0 {
    var neg := set x | x in arr && x < 0 :: x;
    var max := -1;
    var candidate: int :| candidate in neg && forall x :: x in neg ==> x <= candidate;
    assert is_largest_negative(arr, candidate);
  }
}

lemma smallest_positive_properties(arr: seq<int>)
  ensures (exists x :: x in arr && x > 0) ==> 
          (exists x :: is_smallest_positive(arr, x))
{
  if exists x :: x in arr && x > 0 {
    var pos := set x | x in arr && x > 0 :: x;
    var min := 1;
    var candidate: int :| candidate in pos && forall x :: x in pos ==> x >= candidate;
    assert is_smallest_positive(arr, candidate);
  }
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
  a := None;
  b := None;
  
  var largest_neg: int := 0;
  var smallest_pos: int := 0;
  var found_neg: bool := false;
  var found_pos: bool := false;
  
  var i: int := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant found_neg ==> (largest_neg in arr && largest_neg < 0 && forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] <= largest_neg)
    invariant !found_neg ==> forall j :: 0 <= j < i ==> arr[j] >= 0
    invariant found_pos ==> (smallest_pos in arr && smallest_pos > 0 && forall j :: 0 <= j < i && arr[j] > 0 ==> arr[j] >= smallest_pos)
    invariant !found_pos ==> forall j :: 0 <= j < i ==> arr[j] <= 0
  {
    if arr[i] < 0 {
      if !found_neg {
        largest_neg := arr[i];
        found_neg := true;
      } else if arr[i] > largest_neg {
        largest_neg := arr[i];
      }
    } else if arr[i] > 0 {
      if !found_pos {
        smallest_pos := arr[i];
        found_pos := true;
      } else if arr[i] < smallest_pos {
        smallest_pos := arr[i];
      }
    }
    i := i + 1;
  }
  
  if found_neg {
    a := Some(largest_neg);
    largest_negative_properties(arr);
  } else {
    assert forall i :: 0 <= i < |arr| ==> arr[i] >= 0;
  }
  
  if found_pos {
    b := Some(smallest_pos);
    smallest_positive_properties(arr);
  } else {
    assert forall i :: 0 <= i < |arr| ==> arr[i] <= 0;
  }
}
// </vc-code>

