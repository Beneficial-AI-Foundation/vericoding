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
function min5(a: int, b: int, c: int, d: int, e: int): int
    requires a >= 1 && b >= 1 && c >= 1 && d >= 1 && e >= 1
    ensures min5(a, b, c, d, e) == MinCapacity(a, b, c, d, e)
{
    var temp1 := if a <= b then a else b;
    var temp2 := if temp1 <= c then temp1 else c;
    var temp3 := if temp2 <= d then temp2 else d;
    if temp3 <= e then temp3 else e
}

lemma lemma_MinCapacity_positive(A: int, B: int, C: int, D: int, E: int)
    requires A >= 1 && B >= 1 && C >= 1 && D >= 1 && E >= 1
    ensures MinCapacity(A, B, C, D, E) >= 1
{
    // Proof by cases or direct reasoning
    // MinCapacity consists of a series of min operations.
    // If all inputs are >= 1, then the minimum of them must also be >= 1.
}
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
    lemma_MinCapacity_positive(A, B, C, D, E);
    var groups := CeilDiv(N, minCap);
    result := 4 + groups;
}
// </vc-code>

