function power(base: int, exp: int): int
    requires exp >= 0
    ensures exp == 0 ==> power(base, exp) == 1
    ensures base > 0 ==> power(base, exp) > 0
    ensures base != 0 ==> power(base, exp) != 0
    decreases exp
{
    if exp == 0 then 1
    else base * power(base, exp - 1)
}

// <vc-helpers>
lemma power_positive(base: int, exp: int)
    requires exp >= 0 && base > 0
    ensures power(base, exp) > 0
{
    if exp == 0 {
        calc {
            power(base, exp);
            1;
            > 0;
        }
    } else {
        power_positive(base, exp - 1);
        calc {
            power(base, exp);
            base * power(base, exp - 1);
            > 0;
        }
    }
}

lemma division_lemma(a: int, b: int, c: int)
    requires a > 0 && b > 0 && c > 0
    ensures (a * b) / c == b * (a / c)
{
    calc {
        (a * b) / c;
        == { assert a * b == b * a; }
        (b * a) / c;
        == { assert b * (a / c) + b * (a % c) == b * a; }
        b * (a / c) + (b * (a % c)) / c;
        == { assert a % c < c; assert b * (a % c) < b * c; assert (b * (a % c)) / c < b; }
        b * (a / c);
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: int)
    requires n > 0 && k >= 0
    ensures result > 0
    ensures result % n == 0
    ensures result % power(10, k) == 0
    ensures forall m :: m > 0 && m % n == 0 && m % power(10, k) == 0 ==> result <= m
// </vc-spec>
// <vc-code>
{
    var L := n;
    var R := power(10, k);
    assert L > 0;
    assert R > 0;
    while L % R != 0
        invariant L > 0 && R > 0
        invariant L % n == 0
        invariant forall m :: m >= n && m < L && m % n == 0 ==> m % R != 0
        decreases R
    {
        L := L + n;
        calc {
            L / n;
            (n + n) / n;
        }
    }
    result := L;
}
// </vc-code>
// </vc-code>

