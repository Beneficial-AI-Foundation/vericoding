function CountOnesInOctal(a: int): int
    requires a >= 0
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}

// <vc-helpers>
lemma CountOnesInOctalDecreases(a: int)
    requires a >= 0
    ensures CountOnesInOctal(a) >= 0
    decreases a
{
    if a != 0 {
        CountOnesInOctalDecreases(a / 8);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(a: int) returns (count: int)
    requires a >= 0
    ensures count >= 0
    ensures count == CountOnesInOctal(a)
// </vc-spec>
// <vc-code>
{
    count := 0;
    var n := a;
    while n > 0
        invariant n >= 0
        invariant count >= 0
        invariant count + CountOnesInOctal(n) == CountOnesInOctal(a)
        decreases n
    {
        if n % 8 == 1 {
            count := count + 1;
        }
        n := n / 8;
    }
}
// </vc-code>

