predicate ValidInput(n: int)
{
    1 <= n <= 10000
}

predicate ValidChange(change: int)
{
    0 <= change <= 999
}

function CorrectChange(n: int): int
    requires ValidInput(n)
{
    (1000 - n % 1000) % 1000
}

// <vc-helpers>
lemma CorrectChangeProperties(n: int)
    requires ValidInput(n)
    ensures 0 <= CorrectChange(n) <= 999
{
    var remainder := n % 1000;
    assert 0 <= remainder < 1000;
    
    if remainder == 0 {
        assert CorrectChange(n) == 0;
    } else {
        assert CorrectChange(n) == 1000 - remainder;
        assert 1 <= remainder <= 999;
        assert 1 <= 1000 - remainder <= 999;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (change: int)
    requires ValidInput(n)
    ensures ValidChange(change)
    ensures change == CorrectChange(n)
// </vc-spec>
// <vc-code>
{
    CorrectChangeProperties(n);
    var remainder := n % 1000;
    if remainder == 0 {
        change := 0;
    } else {
        change := 1000 - remainder;
    }
}
// </vc-code>

