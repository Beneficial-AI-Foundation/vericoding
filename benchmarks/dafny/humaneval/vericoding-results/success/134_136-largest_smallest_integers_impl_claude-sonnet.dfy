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
/* helper modified by LLM (iteration 4): removed incorrect preconditions from lemmas */
function has_negative(arr: seq<int>): bool {
  exists i :: 0 <= i < |arr| && arr[i] < 0
}

function has_positive(arr: seq<int>): bool {
  exists i :: 0 <= i < |arr| && arr[i] > 0
}

function find_largest_negative(arr: seq<int>): int
  requires exists i :: 0 <= i < |arr| && arr[i] < 0
  ensures find_largest_negative(arr) in arr
  ensures find_largest_negative(arr) < 0
  ensures forall i :: 0 <= i < |arr| && arr[i] < 0 ==> arr[i] <= find_largest_negative(arr)
{
  if |arr| == 1 then arr[0]
  else if arr[0] < 0 then
    if exists i :: 1 <= i < |arr| && arr[i] < 0 then
      var rest := find_largest_negative(arr[1..]);
      if arr[0] >= rest then arr[0] else rest
    else arr[0]
  else
    find_largest_negative(arr[1..])
}

function find_smallest_positive(arr: seq<int>): int
  requires exists i :: 0 <= i < |arr| && arr[i] > 0
  ensures find_smallest_positive(arr) in arr
  ensures find_smallest_positive(arr) > 0
  ensures forall i :: 0 <= i < |arr| && arr[i] > 0 ==> arr[i] >= find_smallest_positive(arr)
{
  if |arr| == 1 then arr[0]
  else if arr[0] > 0 then
    if exists i :: 1 <= i < |arr| && arr[i] > 0 then
      var rest := find_smallest_positive(arr[1..]);
      if arr[0] <= rest then arr[0] else rest
    else arr[0]
  else
    find_smallest_positive(arr[1..])
}
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
  /* code modified by LLM (iteration 4): fixed precondition issues by removing lemma calls */
  if has_negative(arr) {
    a := Some(find_largest_negative(arr));
  } else {
    a := None;
  }
  
  if has_positive(arr) {
    b := Some(find_smallest_positive(arr));
  } else {
    b := None;
  }
}
// </vc-code>
