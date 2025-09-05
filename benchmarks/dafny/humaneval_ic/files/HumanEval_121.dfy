This task requires implementing a method that calculates the sum of all odd numbers located at even-indexed positions in a non-empty sequence of integers. The positions are 0-indexed, so we consider positions 0, 2, 4, etc.

// ======= TASK =======
// Given a non-empty list of integers, return the sum of all odd numbers 
// that are located at even-indexed positions (0, 2, 4, ...).

// ======= SPEC REQUIREMENTS =======
function SumOddAtEvenPositions(lst: seq<int>, pos: int): int
    requires 0 <= pos
    decreases |lst| - pos
{
    if pos >= |lst| then 0
    else if lst[pos] % 2 == 1 then lst[pos] + SumOddAtEvenPositions(lst, pos + 2)
    else SumOddAtEvenPositions(lst, pos + 2)
}

// ======= HELPERS =======

// ======= MAIN METHOD =======
method solution(lst: seq<int>) returns (result: int)
    requires |lst| > 0
    ensures result == SumOddAtEvenPositions(lst, 0)
{
    result := 0;
    var i := 0;
    while i < |lst|
        invariant 0 <= i
        invariant i % 2 == 0
        invariant result + SumOddAtEvenPositions(lst, i) == SumOddAtEvenPositions(lst, 0)
    {
        if lst[i] % 2 == 1 {
            result := result + lst[i];
        }
        i := i + 2;
    }
}
