// <vc-preamble>
predicate ValidInput(a: int, b: int, k: int)
{
    1 <= a <= 1000000000 && 1 <= b <= 1000000000 && 1 <= k <= 1000000000
}

function CalculateFrogPosition(a: int, b: int, k: int): int
{
    var ans := (a - b) * (k / 2);
    if k % 2 == 1 then ans + a else ans
}

function FrogPositionAfterJumps(a: int, b: int, jumps: int): int
    requires jumps >= 0
{
    if jumps == 0 then 0
    else if jumps % 2 == 1 then
        FrogPositionAfterJumps(a, b, jumps - 1) + a
    else
        FrogPositionAfterJumps(a, b, jumps - 1) - b
}
// </vc-preamble>

// <vc-helpers>
lemma CalculationCorrectness(a: int, b: int, k: int)
    requires k >= 0
    ensures CalculateFrogPosition(a, b, k) == FrogPositionAfterJumps(a, b, k)
{
    if k == 0 {
        return;
    }
    if k == 1 {
        return;
    }
    if k % 2 == 0 {
        CalculationCorrectness(a, b, k - 2);
        assert FrogPositionAfterJumps(a, b, k) == FrogPositionAfterJumps(a, b, k - 1) - b;
        assert FrogPositionAfterJumps(a, b, k - 1) == FrogPositionAfterJumps(a, b, k - 2) + a;
        assert FrogPositionAfterJumps(a, b, k) == FrogPositionAfterJumps(a, b, k - 2) + a - b;
        assert (a - b) * (k / 2) == (a - b) * ((k - 2) / 2) + (a - b);
    } else {
        CalculationCorrectness(a, b, k - 2);
        assert FrogPositionAfterJumps(a, b, k) == FrogPositionAfterJumps(a, b, k - 1) + a;
        assert FrogPositionAfterJumps(a, b, k - 1) == FrogPositionAfterJumps(a, b, k - 2) - b;
        assert FrogPositionAfterJumps(a, b, k) == FrogPositionAfterJumps(a, b, k - 2) - b + a;
        assert FrogPositionAfterJumps(a, b, k) == FrogPositionAfterJumps(a, b, k - 2) + a - b;
        assert (a - b) * (k / 2) + a == (a - b) * ((k - 2) / 2) + (a - b) + a;
    }
}
// </vc-helpers>

// <vc-spec>
method FrogJump(a: int, b: int, k: int) returns (position: int)
    requires ValidInput(a, b, k)
    ensures position == CalculateFrogPosition(a, b, k)
    ensures position == FrogPositionAfterJumps(a, b, k)
// </vc-spec>
// <vc-code>
{
    CalculationCorrectness(a, b, k);

    var ans := (a - b) * (k / 2);
    if k % 2 == 1 {
        ans := ans + a;
    }

    position := ans;
}
// </vc-code>
