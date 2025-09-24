// <vc-preamble>
predicate ValidInput(n: int)
{
    1 <= n <= 16
}

function ExpectedResult(n: int): int
    requires ValidInput(n)
{
    if n == 1 then 1
    else if n == 3 then 18
    else if n == 5 then 1800
    else if n == 7 then 670320
    else if n == 9 then 734832000
    else if n == 11 then 890786230
    else if n == 13 then 695720788
    else if n == 15 then 150347555
    else 0
}

predicate CorrectResult(n: int, result: int)
    requires ValidInput(n)
{
    result == ExpectedResult(n)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures CorrectResult(n, result)
// </vc-spec>
// <vc-code>
{
    if n == 1 {
        result := 1;
    } else if n == 3 {
        result := 18;
    } else if n == 5 {
        result := 1800;
    } else if n == 7 {
        result := 670320;
    } else if n == 9 {
        result := 734832000;
    } else if n == 11 {
        result := 890786230;
    } else if n == 13 {
        result := 695720788;
    } else if n == 15 {
        result := 150347555;
    } else {
        result := 0;
    }
}
// </vc-code>
