// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [added proofs for helper lemmas] */
lemma GcdStepProperty(a: nat, b: nat)
    requires b > 0
    ensures forall d: int :: (d > 0 && a % d == 0 && b % d == 0) <==> (d > 0 && b % d == 0 && (a % b) % d == 0)
{
    forall d: int | d > 0
        ensures (a % d == 0 && b % d == 0) <==> (b % d == 0 && (a % b) % d == 0)
    {
        if b % d == 0 {
            if a % d == 0 {
                assert (a % b) % d == 0;
            }
            if (a % b) % d == 0 {
                assert a % d == 0;
            }
        }
    }
}

/* helper modified by LLM (iteration 4): [added proofs for helper lemmas] */
lemma AbsHasSameDivisors(val: int)
    ensures forall d: int :: d > 0 ==> (val % d == 0 <==> (if val < 0 then -val else val) % d == 0)
{
    forall d: int | d > 0
        ensures (val % d == 0 <==> (if val < 0 then -val else val) % d == 0)
    {
        if val >= 0 {
            // trivial, val == abs(val)
        } else { // val < 0
            if val % d == 0 {
                assert (-val) % d == 0;
            }
            if (-val) % d == 0 {
                assert val % d == 0;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method GcdInt(a: int, b: int) returns (result: int)
    ensures
        result > 0 &&
        a % result == 0 &&
        b % result == 0 &&
        (forall d :: d > 0 && a % d == 0 && b % d == 0 ==> d <= result)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [strengthened invariant to handle non-zero case] */
    var x := if a < 0 then -a else a;
    var y := if b < 0 then -b else b;

    AbsHasSameDivisors(a);
    AbsHasSameDivisors(b);

    while y != 0
        invariant x >= 0 && y >= 0
        invariant forall d: int :: (d > 0 && a % d == 0 && b % d == 0) <==> (d > 0 && x % d == 0 && y % d == 0)
        invariant (x == 0 && y == 0) <==> (a == 0 && b == 0)
        decreases y
    {
        assert y > 0;
        GcdStepProperty(x as nat, y as nat);
        var temp := x;
        x := y;
        y := temp % y;
    }
    result := x;
}
// </vc-code>
