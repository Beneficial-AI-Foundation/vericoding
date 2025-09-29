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
lemma ChangeProperties(n: int)
    requires ValidInput(n)
    ensures 0 <= CorrectChange(n) <= 999
{
    var r := n % 1000;
    assert 0 <= r < 1000;
    
    if r == 0 {
        assert CorrectChange(n) == (1000 - 0) % 1000 == 0;
    } else {
        assert 1 <= r <= 999;
        assert 1000 - r >= 1;
        assert 1000 - r <= 999;
        assert CorrectChange(n) == (1000 - r) % 1000 == 1000 - r;
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
    var remainder := n % 1000;
    
    if remainder == 0 {
        change := 0;
    } else {
        change := 1000 - remainder;
    }
    
    ChangeProperties(n);
}
// </vc-code>

