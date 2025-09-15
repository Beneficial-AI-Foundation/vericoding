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
function FindLargestNegative(arr: seq<int>): Option<int>
  ensures FindLargestNegative(arr).None? ==> forall i :: 0 <= i < |arr| ==> arr[i] >= 0
  ensures FindLargestNegative(arr).Some? ==> get_value(FindLargestNegative(arr)) in arr && get_value(FindLargestNegative(arr)) < 0
  ensures FindLargestNegative(arr).Some? ==> forall i :: 0 <= i < |arr| && arr[i] < 0 ==> arr[i] <= get_value(FindLargestNegative(arr))
{
  if |arr| == 0 then None
  else
    var rest := FindLargestNegative(arr[1..]);
    if arr[0] < 0 then
      if rest.None? then Some(arr[0])
      else if arr[0] > get_value(rest) then Some(arr[0])
      else rest
    else rest
}

function FindSmallestPositive(arr: seq<int>): Option<int>
  ensures FindSmallestPositive(arr).None? ==> forall i :: 0 <= i < |arr| ==> arr[i] <= 0
  ensures FindSmallestPositive(arr).Some? ==> get_value(FindSmallestPositive(arr)) in arr && get_value(FindSmallestPositive(arr)) > 0
  ensures FindSmallestPositive(arr).Some? ==> forall i :: 0 <= i < |arr| && arr[i] > 0 ==> arr[i] >= get_value(FindSmallestPositive(arr))
{
  if |arr| == 0 then None
  else
    var rest := FindSmallestPositive(arr[1..]);
    if arr[0] > 0 then
      if rest.None? then Some(arr[0])
      else if arr[0] < get_value(rest) then Some(arr[0])
      else rest
    else rest
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
  a := FindLargestNegative(arr);
  b := FindSmallestPositive(arr);
}
// </vc-code>
