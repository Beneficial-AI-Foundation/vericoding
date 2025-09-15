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
function max_positives(a: int, b: int): int { if a > b && a > 0 then a else if b > 0 then b else a } function min_negatives(a: int, b: int): int { if a < b && a < 0 then a else if b < 0 then b else a } predicate IsPositive(x: int) { x > 0 } predicate IsNegative(x: int) { x < 0 } lemma EnsureLargestNegative(arr: seq<int>, value: int) requires value in arr && value < 0 requires forall i :: 0 <= i < |arr| && arr[i] < 0 ==> arr[i] <= value { } lemma EnsureSmallestPositive(arr: seq<int>, value: int) requires value in arr && value > 0 requires forall i :: 0 <= i < |arr| && arr[i] > 0 ==> arr[i] >= value { }
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
  /* code modified by LLM (iteration 2): Fixing verification errors with proper initialization and loop invariants */
  a := None;
  b := None;
  var largest_negative: int := 0;
  var smallest_positive: int := 0;
  var has_negative := false;
  var has_positive := false;
  
  var i := 0;
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant !has_negative ==> (forall j :: 0 <= j < i ==> arr[j] >= 0)
    invariant has_negative ==> (largest_negative in arr && largest_negative < 0 && (forall j :: 0 <= j < i && arr[j] < 0 ==> arr[j] <= largest_negative))
    invariant !has_positive ==> (forall j :: 0 <= j < i ==> arr[j] <= 0)
    invariant has_positive ==> (smallest_positive in arr && smallest_positive > 0 && (forall j :: 0 <= j < i && arr[j] > 0 ==> arr[j] >= smallest_positive))
  {
    if arr[i] < 0 {
      if !has_negative || arr[i] > largest_negative {
        largest_negative := arr[i];
        has_negative := true;
      }
    } else if arr[i] > 0 {
      if !has_positive || arr[i] < smallest_positive {
        smallest_positive := arr[i];
        has_positive := true;
      }
    }
    i := i + 1;
  }
  
  if has_negative {
    a := Some(largest_negative);
    EnsureLargestNegative(arr, largest_negative);
  }
  if has_positive {
    b := Some(smallest_positive);
    EnsureSmallestPositive(arr, smallest_positive);
  }
}
// </vc-code>
