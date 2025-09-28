// <vc-preamble>
function CountOnesInBinary(n: int): int
    requires n >= 1
    ensures CountOnesInBinary(n) >= 1
    decreases n
{
    if n == 1 then 1
    else if n % 2 == 1 then 1 + CountOnesInBinary(n / 2)
    else CountOnesInBinary(n / 2)
}

predicate ValidInput(x: int) {
    x >= 1
}

predicate ValidOutput(x: int, result: int) {
    ValidInput(x) && result == CountOnesInBinary(x)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): adjusted helper function to match the CountOnesInBinary definition */
function CalculateMinBits(x: int): int
    requires x >= 1
    ensures CalculateMinBits(x) >= 1
    decreases x
{
    if x == 1 then 1
    else if x % 2 == 1 then CalculateMinBits(x / 2) + 1
    else CalculateMinBits(x / 2)
}
// </vc-helpers>

// <vc-spec>
method MinBacteria(x: int) returns (result: int)
    requires ValidInput(x)
    ensures ValidOutput(x, result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): assigned result to CountOnesInBinary(x) */
{
  result := CountOnesInBinary(x);
}
// </vc-code>
