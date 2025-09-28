// <vc-preamble>

function SumOddAtEvenPositions(lst: seq<int>, pos: int): int
    requires 0 <= pos
    decreases |lst| - pos
{
    if pos >= |lst| then 0
    else if lst[pos] % 2 == 1 then lst[pos] + SumOddAtEvenPositions(lst, pos + 2)
    else SumOddAtEvenPositions(lst, pos + 2)
}
// </vc-preamble>

// <vc-helpers>
lemma SumOddAtEvenPositions_unfold(lst: seq<int>, pos: int)
  requires 0 <= pos
  ensures SumOddAtEvenPositions(lst, pos) == (if pos >= |lst| then 0 else if lst[pos] % 2 == 1 then lst[pos] + SumOddAtEvenPositions(lst, pos + 2) else SumOddAtEvenPositions(lst, pos + 2))
{
}

// </vc-helpers>

// <vc-spec>
method solution(lst: seq<int>) returns (result: int)
    requires |lst| > 0
    ensures result == SumOddAtEvenPositions(lst, 0)
// </vc-spec>
// <vc-code>
{
  var pos := 0;
  var acc := 0;
  while pos < |lst|
    decreases |lst| - pos
    invariant 0 <= pos <= |lst|
    invariant acc == SumOddAtEvenPositions(lst, 0) - SumOddAtEvenPositions(lst, pos)
  {
    if lst[pos] % 2 == 1 {
      acc := acc + lst[pos];
    }
    if pos + 2 <= |lst| {
      pos := pos + 2;
    } else {
      pos := |lst|;
    }
  }
  result := acc;
}
// </vc-code>
