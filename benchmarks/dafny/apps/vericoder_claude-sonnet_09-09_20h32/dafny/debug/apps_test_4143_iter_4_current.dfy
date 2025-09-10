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
lemma MinCapacityIsMin(A: int, B: int, C: int, D: int, E: int)
    requires A >= 1 && B >= 1 && C >= 1 && D >= 1 && E >= 1
    ensures MinCapacity(A, B, C, D, E) <= A
    ensures MinCapacity(A, B, C, D, E) <= B
    ensures MinCapacity(A, B, C, D, E) <= C
    ensures MinCapacity(A, B, C, D, E) <= D
    ensures MinCapacity(A, B, C, D, E) <= E
    ensures MinCapacity(A, B, C, D, E) >= 1
{
}

lemma CeilDivProperties(a: int, b: int)
    requires a >= 0 && b >= 1
    ensures CeilDiv(a, b) >= 0
    ensures CeilDiv(a, b) >= (a / b)
    ensures a > 0 ==> CeilDiv(a, b) >= 1
{
    if a == 0 {
        assert CeilDiv(a, b) == (0 + b - 1) / b == (b - 1) / b == 0;
    } else {
        assert a >= 1;
        assert a + b - 1 >= b;
        assert CeilDiv(a, b) == (a + b - 1) / b >= b / b == 1;
    }
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
    MinCapacityIsMin(A, B, C, D, E);
    
    var groups := CeilDiv(N, minCap);
    CeilDivProperties(N, minCap);
    
    result := 4 + groups;
}
// </vc-code>

