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
lemma mod_lemma(n: int)
    requires ValidInput(n)
    ensures (1000 - n % 1000) % 1000 == 1000 - n % 1000
{
    var rem := n % 1000;
    if rem != 0 {
        assert 1000 - rem < 1000;
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
    var rem := n % 1000;
    if rem == 0 {
        change := 0;
    } else {
        change := 1000 - rem;
    }
}
// </vc-code>

