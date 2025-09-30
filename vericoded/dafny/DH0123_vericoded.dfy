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

// </vc-helpers>

// <vc-spec>
method solution(lst: seq<int>) returns (result: int)
    requires |lst| > 0
    ensures result == SumOddAtEvenPositions(lst, 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed loop invariant to allow pos to exceed |lst| */
  result := 0;
  var pos := 0;
  while pos < |lst|
    invariant 0 <= pos <= |lst| + 1
    invariant pos % 2 == 0
    invariant result == SumOddAtEvenPositions(lst, 0) - SumOddAtEvenPositions(lst, pos)
  {
    if lst[pos] % 2 == 1 {
      result := result + lst[pos];
    }
    pos := pos + 2;
  }
}
// </vc-code>
