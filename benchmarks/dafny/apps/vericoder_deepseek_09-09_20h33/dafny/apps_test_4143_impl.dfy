predicate ValidInput(N: int, A: int, B: int, C: int, D: int, E: int)
{
    N >= 1 && A >= 1 && B >= 1 && C >= 1 && D >= 1 && E >= 1
}

function MinCapacity(A: int, B: int, C: int, D: int, E: int): int
    requires A >= 1 && B >= 1 && C >= 1 && D >= 1 && E >= 1
{
    var temp1 := if A <= B then A else B;
    var temp2 := if temp1 <= C then temp1 else C;
    var temp3 := if temp2 <= D then temp2 else D;
    if temp3 <= E then temp3 else E
}

function CeilDiv(a: int, b: int): int
    requires a >= 0 && b >= 1
{
    (a + b - 1) / b
}

predicate CorrectResult(N: int, A: int, B: int, C: int, D: int, E: int, result: int)
    requires ValidInput(N, A, B, C, D, E)
{
    var minCap := MinCapacity(A, B, C, D, E);
    var groups := CeilDiv(N, minCap);
    result == 4 + groups
}

// <vc-helpers>
lemma MinCapacityPositive(A: int, B: int, C: int, D: int, E: int)
    requires A >= 1 && B >= 1 && C >= 1 && D >= 1 && E >= 1
    ensures MinCapacity(A, B, C, D, E) >= 1
{}

lemma CeilDivNonNegative(n: int, d: int)
    requires n >= 0 && d >= 1
    ensures CeilDiv(n, d) >= 0
{}

lemma CeilDivCorrectness(n: int, d: int)
    requires n >= 0 && d >= 1
    ensures CeilDiv(n, d) == (if n == 0 then 0 else (n - 1) / d + 1)
{
    if n == 0 {
        // CeilDiv(0, d) = (0 + d - 1) / d = (d - 1) / d = 0
    } else {
        calc {
            (n + d - 1) / d;
            ==
            (n - 1 + d) / d;
            == { assert (n - 1 + d) / d == (d + (n - 1)) / d; }
            (d + (n - 1)) / d;
            == 
            (n - 1) / d + 1;
        }
    }
}

lemma CeilDivCorrectnessAlt(n: int, d: int)
    requires n >= 0 && d >= 1
    ensures CeilDiv(n, d) >= (n + d - 1) / d
{
    // This simpler lemma avoids the complex calculation
}

lemma CeilDivMinimal(n: int, d: int)
    requires n >= 0 && d >= 1
    ensures CeilDiv(n, d) >= 0
    ensures n == 0 ==> CeilDiv(n, d) == 0
    ensures n > 0 ==> CeilDiv(n, d) >= 1
{
    if n == 0 {
    } else {
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(N: int, A: int, B: int, C: int, D: int, E: int) returns (result: int)
    requires ValidInput(N, A, B, C, D, E)
    ensures CorrectResult(N, A, B, C, D, E, result)
    ensures result >= 5
// </vc-spec>
// <vc-code>
{
    var minCap := MinCapacity(A, B, C, D, E);
    MinCapacityPositive(A, B, C, D, E);
    var groups := CeilDiv(N, minCap);
    CeilDivNonNegative(N, minCap);
    CeilDivCorrectnessAlt(N, minCap);
    CeilDivMinimal(N, minCap);
    assert minCap >= 1;
    result := 4 + groups;
}
// </vc-code>

