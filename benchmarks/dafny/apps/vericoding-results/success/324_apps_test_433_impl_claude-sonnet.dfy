predicate ValidInput(n: int, a: int, b: int) {
    n >= 1 && 1 <= a <= n && -100 <= b <= 100
}

function FinalEntrance(n: int, a: int, b: int): int
    requires ValidInput(n, a, b)
{
    ((a - 1 + b) % n + n) % n + 1
}

predicate ValidOutput(result: int, n: int) {
    1 <= result <= n
}

// <vc-helpers>
lemma ModuloProperties(x: int, n: int)
    requires n > 0
    ensures (x % n + n) % n >= 0
    ensures (x % n + n) % n < n
{
}

lemma FinalEntranceInRange(n: int, a: int, b: int)
    requires ValidInput(n, a, b)
    ensures 1 <= FinalEntrance(n, a, b) <= n
{
    var temp := (a - 1 + b) % n;
    var normalized := (temp + n) % n;
    ModuloProperties(a - 1 + b, n);
    assert 0 <= normalized < n;
    assert FinalEntrance(n, a, b) == normalized + 1;
    assert 1 <= normalized + 1 <= n;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, a, b)
    ensures ValidOutput(result, n)
    ensures result == FinalEntrance(n, a, b)
// </vc-spec>
// <vc-code>
{
    var temp := (a - 1 + b) % n;
    var normalized := (temp + n) % n;
    result := normalized + 1;
    
    FinalEntranceInRange(n, a, b);
}
// </vc-code>

