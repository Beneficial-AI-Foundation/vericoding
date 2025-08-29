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

function FilterNegatives(lst: seq<int>): seq<int>
{
  seq i | 0 <= i < |lst| && IsNegative(lst[i]) :: lst[i]
}

function FilterPositives(lst: seq<int>): seq<int>
{
  seq i | 0 <= i < |lst| && IsPositive(lst[i]) :: lst[i]
}

function MaxOfSeq(s: seq<int>): int
  requires |s| > 0
  ensures MaxOfSeq(s) in s
  ensures forall x :: x in s ==> x <= MaxOfSeq(s)
{
  if |s| == 1 then s[0]
  else if s[0] >= MaxOfSeq(s[1..]) then s[0]
  else MaxOfSeq(s[1..])
}

function MinOfSeq(s: seq<int>): int
  requires |s| > 0
  ensures MinOfSeq(s) in s
  ensures forall x :: x in s ==> x >= MinOfSeq(s)
{
  if |s| == 1 then s[0]
  else if s[0] <= MinOfSeq(s[1..]) then s[0]
  else MinOfSeq(s[1..])
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def largest_smallest_integers(lst: List[int]) -> Tuple[ Optional[Int], Optional[Int] ]
Create a function that returns a tuple (a, b), where 'a' is the largest of negative integers, and 'b' is the smallest of positive integers in a list. If there is no negative or positive integers, return them as None.
*/
// </vc-description>

// <vc-code>
method largest_smallest_integers(lst: seq<int>) returns (largest_negative: Option<int>, smallest_positive: Option<int>)
  ensures largest_negative.Some? ==> (
    largest_negative.value < 0 &&
    largest_negative.value in lst &&
    forall x :: x in lst && x < 0 ==> x <= largest_negative.value
  )
  ensures largest_negative.None? ==> forall x :: x in lst ==> x >= 0
  ensures smallest_positive.Some? ==> (
    smallest_positive.value > 0 &&
    smallest_positive.value in lst &&
    forall x :: x in lst && x > 0 ==> x >= smallest_positive.value
  )
  ensures smallest_positive.None? ==> forall x :: x in lst ==> x <= 0
{
  var negatives := FilterNegatives(lst);
  var positives := FilterPositives(lst);
  
  if |negatives| == 0 {
    largest_negative := None;
  } else {
    largest_negative := Some(MaxOfSeq(negatives));
  }
  
  if |positives| == 0 {
    smallest_positive := None;
  } else {
    smallest_positive := Some(MinOfSeq(positives));
  }
}
// </vc-code>
