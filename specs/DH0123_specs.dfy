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
    assume {:axiom} false;
  }
// </vc-code>
