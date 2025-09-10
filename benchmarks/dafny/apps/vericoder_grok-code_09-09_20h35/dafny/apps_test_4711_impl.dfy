predicate ValidInput(a: int, b: int, c: int) {
    1 <= a <= 10000 && 1 <= b <= 10000 && 1 <= c <= 10000
}

function MinOfThree(x: int, y: int, z: int): int {
    if x <= y && x <= z then x
    else if y <= z then y
    else z
}

function CorrectResult(a: int, b: int, c: int): int {
    MinOfThree(a + b, a + c, b + c)
}

// <vc-helpers>
// No additional helpers needed
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures result == CorrectResult(a, b, c)
// </vc-spec>
// <vc-code>
{
  result := MinOfThree(a + b, a + c, b + c);
}
// </vc-code>

