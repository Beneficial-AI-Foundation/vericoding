// <vc-helpers>
function sumOddAtEvenPositions(s: seq<int>): int {
  if |s| <= 1 then 0
  else if |s| % 2 == 0 then (if s[1] % 2 == 1 then s[1] else 0) + sumOddAtEvenPositions(s[2..])
  else sumOddAtEvenPositions(s[2..])
}

function sumFiltered(s: seq<int>, filter: seq<bool>): int
  requires |s| == |filter|
{
  if |s| == 0 then 0
  else (if filter[0] then s[0] else 0) + sumFiltered(s[1..], filter[1..])
}

lemma SumOddAtEvenPositionsCorrect(s: seq<int>)
  ensures sumOddAtEvenPositions(s) == sumFiltered(s, seq(|s|, i => i < |s| && i % 2 == 1))
{
  if |s| <= 1 {
    assert sumOddAtEvenPositions(s) == 0;
    assert sumFiltered(s, seq(|s|, i => i < |s| && i % 2 == 1)) == 0;
  } else {
    assert |s| >= 2;
    var filter := seq(|s|, i => i < |s| && i % 2 == 1);
    var filterTail := seq(|s[2..]|, i => i < |s[2..]| && (i + 2) % 2 == 1);
    SumOddAtEvenPositionsCorrect(s[2..]);
    assert sumOddAtEvenPositions(s[2..]) == sumFiltered(s[2..], filterTail);
    if |s| % 2 == 0 {
      assert filter[1] == (1 % 2 == 1);
      assert sumOddAtEvenPositions(s) == (if s[1] % 2 == 1 then s[1] else 0) + sumOddAtEvenPositions(s[2..]);
      assert sumFiltered(s, filter) == (if filter[1] && s[1] % 2 == 1 then s[1] else 0) + sumFiltered(s[2..], filter[2..]);
    } else {
      assert sumOddAtEvenPositions(s) == sumOddAtEvenPositions(s[2..]);
      assert sumFiltered(s, filter) == sumFiltered(s[2..], filter[2..]);
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def solution(lst: List[int]) -> int
Given a non-empty list of integers, return the sum of all of the odd elements that are in even positions.
*/
// </vc-description>

// <vc-spec>
method solution(lst: seq<int>) returns (result: int)
  requires |lst| > 0
  ensures result == sumOddAtEvenPositions(lst)
// </vc-spec>
// <vc-code>
{
  var sum := 0;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant sum == sumFiltered(lst[..i], seq(i, j => j < i && j % 2 == 1))
  {
    if i % 2 == 1 && lst[i] % 2 == 1 {
      sum := sum + lst[i];
    }
    i := i + 1;
  }
  result := sum;
}
// </vc-code>

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end