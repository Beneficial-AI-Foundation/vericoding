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
{
  if |lst| == 0 then None
  else if IsNegative(lst[0]) then
    var rest := FindLargestNegative(lst[1..]);
    if rest.None? then Some(lst[0])
    else Some(if lst[0] > rest.value then lst[0] else rest.value)
  else
    FindLargestNegative(lst[1..])
}

function FindSmallestPositive(lst: seq<int>): Option<int>
{
  if |lst| == 0 then None
  else if IsPositive(lst[0]) then
    var rest := FindSmallestPositive(lst[1..]);
    if rest.None? then Some(lst[0])
    else Some(if lst[0] < rest.value then lst[0] else rest.value)
  else
    FindSmallestPositive(lst[1..])
}

lemma FindLargestNegativeCorrect(lst: seq<int>)
  ensures var result := FindLargestNegative(lst);
    result.Some? ==> IsNegative(result.value) && result.value in lst &&
    forall x :: x in lst && IsNegative(x) ==> x <= result.value
  ensures var result := FindLargestNegative(lst);
    result.None? ==> forall x :: x in lst ==> !IsNegative(x)

lemma FindSmallestPositiveCorrect(lst: seq<int>)
  ensures var result := FindSmallestPositive(lst);
    result.Some? ==> IsPositive(result.value) && result.value in lst &&
    forall x :: x in lst && IsPositive(x) ==> x >= result.value
  ensures var result := FindSmallestPositive(lst);
    result.None? ==> forall x :: x in lst ==> !IsPositive(x)
// </vc-helpers>

// <vc-description>
/*
function_signature: def largest_smallest_integers(lst: List[int]) -> Tuple[ Optional[Int], Optional[Int] ]
Create a function that returns a tuple (a, b), where 'a' is the largest of negative integers, and 'b' is the smallest of positive integers in a list. If there is no negative or positive integers, return them as None.
*/
// </vc-description>

// <vc-spec>
method largest_smallest_integers(lst: seq<int>) returns (largest_neg: Option<int>, smallest_pos: Option<int>)
  ensures largest_neg.Some? ==> largest_neg.value < 0 && largest_neg.value in lst
  ensures largest_neg.Some? ==> forall x :: x in lst && x < 0 ==> x <= largest_neg.value
  ensures largest_neg.None? ==> forall x :: x in lst ==> x >= 0
  ensures smallest_pos.Some? ==> smallest_pos.value > 0 && smallest_pos.value in lst
  ensures smallest_pos.Some? ==> forall x :: x in lst && x > 0 ==> x >= smallest_pos.value
  ensures smallest_pos.None? ==> forall x :: x in lst ==> x <= 0
// </vc-spec>
// <vc-code>
method largest_smallest_integers(lst: seq<int>) returns (largest_neg: Option<int>, smallest_pos: Option<int>)
  ensures largest_neg.Some? ==> largest_neg.value < 0 && largest_neg.value in lst
  ensures largest_neg.Some? ==> forall x :: x in lst && x < 0 ==> x <= largest_neg.value
  ensures largest_neg.None? ==> forall x :: x in lst ==> x >= 0
  ensures smallest_pos.Some? ==> smallest_pos.value > 0 && smallest_pos.value in lst
  ensures smallest_pos.Some? ==> forall x :: x in lst && x > 0 ==> x >= smallest_pos.value
  ensures smallest_pos.None? ==> forall x :: x in lst ==> x <= 0
{
  FindLargestNegativeCorrect(lst);
  FindSmallestPositiveCorrect(lst);
  largest_neg := FindLargestNegative(lst);
  smallest_pos := FindSmallestPositive(lst);
}
// </vc-code>
