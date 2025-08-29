datatype Option<T> = None | Some(value: T)
function get_value(o: Option<int>): int
  requires o.Some?
  ensures get_value(o) == o.value
{
  o.value
}

// <vc-helpers>
lemma LemmaMaxNegativeExists(arr: seq<int>)
  requires exists i :: 0 <= i < |arr| && arr[i] < 0
  ensures exists i :: 0 <= i < |arr| && arr[i] < 0 && forall j :: 0 <= j < |arr| && arr[j] < 0 ==> arr[j] <= arr[i]
{
  var negatives := set i | 0 <= i < |arr| && arr[i] < 0 :: arr[i];
  assert negatives != {};
  var max_neg := MaxOfSet(negatives);
  assert max_neg in negatives;
}

lemma LemmaMinPositiveExists(arr: seq<int>)
  requires exists i :: 0 <= i < |arr| && arr[i] > 0
  ensures exists i :: 0 <= i < |arr| && arr[i] > 0 && forall j :: 0 <= j < |arr| && arr[j] > 0 ==> arr[j] >= arr[i]
{
  var positives := set i | 0 <= i < |arr| && arr[i] > 0 :: arr[i];
  assert positives != {};
  var min_pos := MinOfSet(positives);
  assert min_pos in positives;
}

function MaxOfSet(s: set<int>): int
  requires s != {}
  ensures MaxOfSet(s) in s
  ensures forall x :: x in s ==> x <= MaxOfSet(s)

function MinOfSet(s: set<int>): int
  requires s != {}
  ensures MinOfSet(s) in s
  ensures forall x :: x in s ==> x >= MinOfSet(s)
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
  var max_negative: Option<int> := None;
  var min_positive: Option<int> := None;
  
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant max_negative.None? ==> forall j :: 0 <= j < i ==> arr[j] >= 0
    invariant max_negative.Some? ==> get_value(max_negative) in arr[..i] && get_value(max_negative) < 0
    invariant max_negative.Some? ==> forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] <= get_value(max_negative)
    invariant min_positive.None? ==> forall j :: 0 <= j < i ==> arr[j] <= 0
    invariant min_positive.Some? ==> get_value(min_positive) in arr[..i] && get_value(min_positive) > 0
    invariant min_positive.Some? ==> forall j :: 0 <= j < i && arr[j] > 0 ==> arr[j] >= get_value(min_positive)
  {
    if arr[i] < 0 {
      if max_negative.None? || arr[i] > get_value(max_negative) {
        max_negative := Some(arr[i]);
      }
    } else if arr[i] > 0 {
      if min_positive.None? || arr[i] < get_value(min_positive) {
        min_positive := Some(arr[i]);
      }
    }
    i := i + 1;
  }
  
  a := max_negative;
  b := min_positive;
}
// </vc-code>

