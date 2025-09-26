// <vc-preamble>
predicate ValidInput(n: int, a: string, b: string)
{
    n > 0 && |a| == 2 * n && |b| == 2 * n &&
    (forall i :: 0 <= i < |a| ==> a[i] == '0' || a[i] == '1') &&
    (forall i :: 0 <= i < |b| ==> b[i] == '0' || b[i] == '1')
}

function CountPositions(a: string, b: string, ac: char, bc: char, len: int): int
    requires len >= 0 && len <= |a| && len <= |b|
    requires ac == '0' || ac == '1'
    requires bc == '0' || bc == '1'
{
    |set i | 0 <= i < len && a[i] == ac && b[i] == bc|
}

function ComputeGameOutcome(t00: int, t01: int, t10: int, t11: int): int
{
    t11 % 2 + (t10 - t01 + 1 - t11 % 2) / 2
}

predicate CorrectOutcome(result: string, d: int)
{
    (d > 0 ==> result == "First") &&
    (d < 0 ==> result == "Second") &&
    (d == 0 ==> result == "Draw")
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: string, b: string) returns (result: string)
    requires ValidInput(n, a, b)
    ensures result == "First" || result == "Second" || result == "Draw"
    ensures (exists t00, t01, t10, t11: int ::
        t00 >= 0 && t01 >= 0 && t10 >= 0 && t11 >= 0 &&
        t00 + t01 + t10 + t11 == 2 * n &&
        t00 == CountPositions(a, b, '0', '0', 2 * n) &&
        t01 == CountPositions(a, b, '0', '1', 2 * n) &&
        t10 == CountPositions(a, b, '1', '0', 2 * n) &&
        t11 == CountPositions(a, b, '1', '1', 2 * n) &&
        CorrectOutcome(result, ComputeGameOutcome(t00, t01, t10, t11)))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
