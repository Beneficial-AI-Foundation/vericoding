This verification task implements a function that computes the sum of squares of all positive odd integers in a list containing both integers and real numbers. The function should ignore negative numbers and non-integers, returning 0 for an empty list.

The implementation needs to handle a mixed datatype that can represent both integers and reals, properly identify positive odd integers (including reals that represent integers), and maintain correctness through loop invariants.

// ======= TASK =======
// Given a list of numbers, return the sum of squares of all positive odd integers in the list. 
// Ignore negative numbers and non-integers. Return 0 for an empty list.

// ======= SPEC REQUIREMENTS =======
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

// ======= HELPERS =======

// ======= MAIN METHOD =======
method double_the_difference(lst: seq<Number>) returns (result: int)
    ensures result >= 0
    ensures result == SumOfSquares(lst, |lst|)
    ensures |lst| == 0 ==> result == 0
{
    result := 0;
    for i := 0 to |lst|
        invariant result == SumOfSquares(lst, i)
    {
        match lst[i]
        case Int(n) =>
            if n > 0 && n % 2 == 1 {
                result := result + n * n;
            }
        case Real(r) =>
            if IsInteger(r) && r > 0.0 && (r.Floor as int) % 2 == 1 {
                result := result + (r.Floor as int) * (r.Floor as int);
            }
    }
}
