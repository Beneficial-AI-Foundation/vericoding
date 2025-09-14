function R(n: nat): nat {
    if n == 0 then 0 else if R(n-1) > n then R(n-1) - n else R(n-1) + n
}

// <vc-helpers>
lemma RProperty(n: nat)
    ensures R(n) <= n * (n + 1) / 2
    decreases n
{
    if n > 0 {
        RProperty(n-1);
        var prev := R(n-1);
        if prev > n {
            assert R(n) == prev - n;
        } else {
            assert R(n) == prev + n;
        }
    }
}

lemma RMonotonic(n: nat)
    ensures n > 0 ==> R(n) >= R(n-1) - n
    decreases n
{
    if n > 0 {
        RMonotonic(n-1);
        // Prove that R(n) >= R(n-1) - n
        var prev := R(n-1);
        if prev > n {
            assert R(n) == prev - n;
            assert R(n) >= prev - n;
        } else {
            assert R(n) == prev + n;
            assert prev + n >= prev - n;
        }
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method calcR(n: nat) returns (r: nat)
    ensures r == R(n)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        r := 0;
    } else {
        var prev := calcR(n-1);
        if prev > n {
            r := prev - n;
        } else {
            r := prev + n;
        }
    }
}
// </vc-code>

