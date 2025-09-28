// <vc-preamble>

predicate ValidInput(number: real)
{
    number >= 0.0
}

predicate ValidOutput(result: real, input: real)
{
    0.0 <= result < 1.0 && result == input - Floor(input)
}

function Floor(x: real): real
    ensures Floor(x) <= x < Floor(x) + 1.0
{
    if x >= 0.0 then
        FloorNonnegative(x)
    else
        -CeilNonnegative(-x)
}

function FloorNonnegative(x: real): real
    requires x >= 0.0
    ensures FloorNonnegative(x) <= x < FloorNonnegative(x) + 1.0
    ensures FloorNonnegative(x) >= 0.0
{
    FloorHelper(x, 0)
}

function FloorHelper(x: real, n: int): real
    requires x >= 0.0
    requires n >= 0
    ensures FloorHelper(x, n) <= x + n as real < FloorHelper(x, n) + 1.0
    ensures FloorHelper(x, n) >= n as real
    decreases x
{
    if x < 1.0 then 
        n as real
    else 
        FloorHelper(x - 1.0, n + 1)
}

function CeilNonnegative(x: real): real
    requires x >= 0.0
    ensures CeilNonnegative(x) >= x
    ensures x > 0.0 ==> CeilNonnegative(x) < x + 1.0
{
    if x == 0.0 then 
        0.0
    else if FloorNonnegative(x) == x then
        x
    else
        FloorNonnegative(x) + 1.0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method truncate_number(number: real) returns (result: real)
    requires ValidInput(number)
    ensures ValidOutput(result, number)
// </vc-spec>
// <vc-code>
{
  result := number - Floor(number);
}
// </vc-code>
