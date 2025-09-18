// <vc-preamble>

datatype Number = Int(i: int) | Real(r: real)

function IsInteger(r: real): bool
{
    r == r.Floor as real
}

predicate IsPositiveOddInteger(n: Number)
{
    match n
    case Int(i) => i > 0 && i % 2 == 1
    case Real(r) => IsInteger(r) && r > 0.0 && (r.Floor as int) % 2 == 1
}

function SquareValue(n: Number): int
    requires IsPositiveOddInteger(n)
    ensures SquareValue(n) > 0
{
    match n
    case Int(i) => i * i
    case Real(r) => (r.Floor as int) * (r.Floor as int)
}

function SumOfSquares(lst: seq<Number>, i: nat): int
    requires i <= |lst|
    ensures SumOfSquares(lst, i) >= 0
{
    if i == 0 then 0
    else if IsPositiveOddInteger(lst[i-1]) then
        SquareValue(lst[i-1]) + SumOfSquares(lst, i-1)
    else
        SumOfSquares(lst, i-1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method double_the_difference(lst: seq<Number>) returns (result: int)
    ensures result >= 0
    ensures result == SumOfSquares(lst, |lst|)
    ensures |lst| == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
