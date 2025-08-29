datatype Option<T> = None | Some(value: T)
function get_value(o: Option<int>): int
  requires o.Some?
  ensures get_value(o) == o.value
{
  o.value
}

// <vc-helpers>
// Helper function to check if a list has negative numbers
predicate HasNegative(lst: seq<int>)
{
  exists i :: 0 <= i < |lst| && lst[i] < 0
}

// Helper function to check if a list has positive numbers
predicate HasPositive(lst: seq<int>)
{
  exists i :: 0 <= i < |lst| && lst[i] > 0
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def largest_smallest_integers(lst: List[int]) -> Tuple[ Optional[Int], Optional[Int] ]
Create a function that returns a tuple (a, b), where 'a' is the largest of negative integers, and 'b' is the smallest of positive integers in a list. If there is no negative or positive integers, return them as None.
*/
// </vc-description>

// <vc-spec>
method LargestSmallestIntegers(lst: seq<int>) returns (largestNeg: Option<int>, smallestPos: Option<int>)
  ensures HasNegative(lst) ==> largestNeg.Some? && forall i :: 0 <= i < |lst| && lst[i] < 0 ==> lst[i] <= largestNeg.value
  ensures HasNegative(lst) ==> exists i :: 0 <= i < |lst| && lst[i] == largestNeg.value
  ensures !HasNegative(lst) ==> largestNeg.None?
  ensures HasPositive(lst) ==> smallestPos.Some? && forall i :: 0 <= i < |lst| && lst[i] > 0 ==> lst[i] >= smallestPos.value
  ensures HasPositive(lst) ==> exists i :: 0 <= i < |lst| && lst[i] == smallestPos.value
  ensures !HasPositive(lst) ==> smallestPos.None?
// </vc-spec>
// <vc-code>
{
  var neg: Option<int> := None;
  var pos: Option<int> := None;
  
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant neg.Some? ==> neg.value < 0
    invariant neg.Some? ==> exists k :: 0 <= k < i && lst[k] == neg.value
    invariant neg.Some? ==> forall k :: 0 <= k < i && lst[k] < 0 ==> lst[k] <= neg.value
    invariant pos.Some? ==> pos.value > 0
    invariant pos.Some? ==> exists k :: 0 <= k < i && lst[k] == pos.value
    invariant pos.Some? ==> forall k :: 0 <= k < i && lst[k] > 0 ==> lst[k] >= pos.value
  {
    if lst[i] < 0 {
      if neg.None? || lst[i] > neg.value {
        neg := Some(lst[i]);
      }
    } else if lst[i] > 0 {
      if pos.None? || lst[i] < pos.value {
        pos := Some(lst[i]);
      }
    }
    i := i + 1;
  }
  
  largestNeg := neg;
  smallestPos := pos;
}
// </vc-code>
