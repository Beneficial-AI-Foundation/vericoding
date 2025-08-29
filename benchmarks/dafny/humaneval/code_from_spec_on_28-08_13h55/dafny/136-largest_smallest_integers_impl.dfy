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
  if |lst| == 0 then []
  else if lst[0] < 0 then [lst[0]] + FilterNegatives(lst[1..])
  else FilterNegatives(lst[1..])
}

function FilterPositives(lst: seq<int>): seq<int>
{
  if |lst| == 0 then []
  else if lst[0] > 0 then [lst[0]] + FilterPositives(lst[1..])
  else FilterPositives(lst[1..])
}

function MaxOfSeq(s: seq<int>): int
  requires |s| > 0
  ensures MaxOfSeq(s) in s
  ensures forall x :: x in s ==> x <= MaxOfSeq(s)
  decreases |s|
{
  if |s| == 1 then s[0]
  else if s[0] >= MaxOfSeq(s[1..]) then 
    assert s[0] in s;
    assert forall x :: x in s[1..] ==> x in s;
    s[0]
  else 
    assert MaxOfSeq(s[1..]) in s[1..];
    assert MaxOfSeq(s[1..]) in s;
    assert forall x :: x in s[1..] ==> x <= MaxOfSeq(s[1..]);
    assert s[0] < MaxOfSeq(s[1..]);
    MaxOfSeq(s[1..])
}

function MinOfSeq(s: seq<int>): int
  requires |s| > 0
  ensures MinOfSeq(s) in s
  ensures forall x :: x in s ==> x >= MinOfSeq(s)
  decreases |s|
{
  if |s| == 1 then s[0]
  else if s[0] <= MinOfSeq(s[1..]) then
    assert s[0] in s;
    assert forall x :: x in s[1..] ==> x in s;
    s[0]
  else
    assert MinOfSeq(s[1..]) in s[1..];
    assert MinOfSeq(s[1..]) in s;
    assert forall x :: x in s[1..] ==> x >= MinOfSeq(s[1..]);
    assert s[0] > MinOfSeq(s[1..]);
    MinOfSeq(s[1..])
}

lemma FilterNegativesProperties(lst: seq<int>)
  ensures forall x :: x in FilterNegatives(lst) ==> x in lst && x < 0
  ensures forall i :: 0 <= i < |lst| && lst[i] < 0 ==> lst[i] in FilterNegatives(lst)
{
  if |lst| == 0 {
    // Base case
  } else {
    FilterNegativesProperties(lst[1..]);
    if lst[0] < 0 {
      assert lst[0] in FilterNegatives(lst);
    }
  }
}

lemma FilterPositivesProperties(lst: seq<int>)
  ensures forall x :: x in FilterPositives(lst) ==> x in lst && x > 0
  ensures forall i :: 0 <= i < |lst| && lst[i] > 0 ==> lst[i] in FilterPositives(lst)
{
  if |lst| == 0 {
    // Base case
  } else {
    FilterPositivesProperties(lst[1..]);
    if lst[0] > 0 {
      assert lst[0] in FilterPositives(lst);
    }
  }
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
  var has_negative := false;
  var has_positive := false;
  var max_negative := 0;
  var min_positive := 0;
  
  for i := 0 to |lst|
    invariant has_negative ==> (max_negative < 0 && max_negative in lst[0..i] && forall x :: x in lst[0..i] && x < 0 ==> x <= max_negative)
    invariant !has_negative ==> forall x :: x in lst[0..i] ==> x >= 0
    invariant has_positive ==> (min_positive > 0 && min_positive in lst[0..i] && forall x :: x in lst[0..i] && x > 0 ==> x >= min_positive)
    invariant !has_positive ==> forall x :: x in lst[0..i] ==> x <= 0
  {
    if lst[i] < 0 {
      if !has_negative || lst[i] > max_negative {
        max_negative := lst[i];
        has_negative := true;
      } else {
        has_negative := true;
      }
    } else if lst[i] > 0 {
      if !has_positive || lst[i] < min_positive {
        min_positive := lst[i];
        has_positive := true;
      } else {
        has_positive := true;
      }
    }
  }
  
  if has_negative {
    largest_negative := Some(max_negative);
  } else {
    largest_negative := None;
  }
  
  if has_positive {
    smallest_positive := Some(min_positive);
  } else {
    smallest_positive := None;
  }
}
// </vc-code>
