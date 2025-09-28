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
function SumOfSquaresHelper(lst: seq<Number>, index: int, acc: int): int
    requires 0 <= index <= |lst|
    requires acc >= 0
    ensures SumOfSquaresHelper(lst, index, acc) >= 0
    ensures SumOfSquaresHelper(lst, index, acc) == acc + SumOfSquares(lst, index)
{
    if index == 0 then
        acc
    else
        var prev := index - 1;
        if IsPositiveOddInteger(lst[prev]) then
            var square := SquareValue(lst[prev]);
            SumOfSquaresHelper(lst, prev, acc + square)
        else
            SumOfSquaresHelper(lst, prev, acc)
}
// </vc-helpers>

// <vc-spec>
method double_the_difference(lst: seq<Number>) returns (result: int)
    ensures result >= 0
    ensures result == SumOfSquares(lst, |lst|)
    ensures |lst| == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
    result := SumOfSquaresHelper(lst, |lst|, 0);
}
// </vc-code>
