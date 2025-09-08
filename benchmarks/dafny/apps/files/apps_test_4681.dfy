Compute the N-th Lucas number where the Lucas sequence is defined as:
L₀ = 2, L₁ = 1, and Lᵢ = Lᵢ₋₁ + Lᵢ₋₂ for i ≥ 2

function Lucas(n: int): int
    requires n >= 0
{
    if n == 0 then 2
    else if n == 1 then 1
    else Lucas(n-1) + Lucas(n-2)
}

predicate ValidInput(n: int) {
    1 <= n <= 86
}

method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result == Lucas(n)
{
    var a := 2;
    var b := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant a == Lucas(i) && b == Lucas(i+1)
    {
        var nxt := a + b;
        a := b;
        b := nxt;
        i := i + 1;
    }
    result := a;
}
