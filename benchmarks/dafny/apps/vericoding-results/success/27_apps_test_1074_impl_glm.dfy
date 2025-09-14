function CountOnesInOctal(a: int): int
    requires a >= 0
{
    if a == 0 then 0
    else (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
}

// <vc-helpers>
lemma CountOnesInOctal_div_8(a: int)
    requires a >= 0
    ensures CountOnesInOctal(a) == (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8)
{
    if a == 0 {
        calc {
            CountOnesInOctal(a);
            0;
            (if a % 8 == 1 then 1 else 0) + 0;
            (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8);
        }
    } else {
        calc {
            CountOnesInOctal(a);
            (if a % 8 == 1 then 1 else 0) + CountOnesInOctal(a / 8);
        }
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
        invariant count + CountOnesInOctal(n) == CountOnesInOctal(a)
    {
        CountOnesInOctal_div_8(n);
        count := count + (if n % 8 == 1 then 1 else 0);
        n := n / 8;
    }
}
// </vc-code>

