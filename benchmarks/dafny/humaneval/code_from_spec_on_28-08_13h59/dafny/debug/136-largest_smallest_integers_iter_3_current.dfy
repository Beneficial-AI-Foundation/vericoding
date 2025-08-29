datatype Option<T> = None | Some(value: T)
function get_value(o: Option<int>): int
  requires o.Some?
  ensures get_value(o) == o.value
{
  o.value
}

// <vc-helpers>
predicate IsNegative(x: int) { x < 0 }
predicate IsPositive(x: int) { x > 0 }

function FindLargestNegative(lst: seq<int>): Option<int>
  ensures FindLargestNegative(lst).Some? ==> IsNegative(FindLargestNegative(lst).value)
  ensures FindLargestNegative(lst).Some? ==> FindLargestNegative(lst).value in lst
  ensures FindLargestNegative(lst).Some? ==> forall x :: x in lst && IsNegative(x) ==> x <= FindLargestNegative(lst).value
  ensures FindLargestNegative(lst).None? ==> forall x :: x in lst ==> !IsNegative(x)
{
  if |lst| == 0 then None
  else
    var rest := FindLargestNegative(lst[1..]);
    if IsNegative(lst[0]) then
      if rest.Some? then
        if lst[0] > rest.value then Some(lst[0]) else rest
      else
        Some(lst[0])
    else
      rest
}

function FindSmallestPositive(lst: seq<int>): Option<int>
  ensures FindSmallestPositive(lst).Some? ==> IsPositive(FindSmallestPositive(lst).value)
  ensures FindSmallestPositive(lst).Some? ==> FindSmallestPositive(lst).value in lst
  ensures FindSmallestPositive(lst).Some? ==> forall x :: x in lst && IsPositive(x) ==> x >= FindSmallestPositive(lst).value
  ensures FindSmallestPositive(lst).None? ==> forall x :: x in lst ==> !IsPositive(x)
{
  if |lst| == 0 then None
  else
    var rest := FindSmallestPositive(lst[1..]);
    if IsPositive(lst[0]) then
      if rest.Some? then
        if lst[0] < rest.value then Some(lst[0]) else rest
      else
        Some(lst[0])
    else
      rest
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def largest_smallest_integers(lst: List[int]) -> Tuple[ Optional[Int], Optional[Int] ]
Create a function that returns a tuple (a, b), where 'a' is the largest of negative integers, and 'b' is the smallest of positive integers in a list. If there is no negative or positive integers, return them as None.
*/
// </vc-description>

// <vc-spec>
method largest_smallest_integers(lst: seq<int>) returns (result: (Option<int>, Option<int>))
  ensures result.0.Some? ==> IsNegative(result.0.value) && result.0.value in lst
  ensures result.0.Some? ==> forall x :: x in lst && IsNegative(x) ==> x <= result.0.value
  ensures result.0.None? ==> forall x :: x in lst ==> !IsNegative(x)
  ensures result.1.Some? ==> IsPositive(result.1.value) && result.1.value in lst
  ensures result.1.Some? ==> forall x :: x in lst && IsPositive(x) ==> x >= result.1.value
  ensures result.1.None? ==> forall x :: x in lst ==> !IsPositive(x)
// </vc-spec>
// <vc-code>
{
  var largestNegative := FindLargestNegative(lst);
  var smallestPositive := FindSmallestPositive(lst);
  result := (largestNegative, smallestPositive);
}
// </vc-code>
