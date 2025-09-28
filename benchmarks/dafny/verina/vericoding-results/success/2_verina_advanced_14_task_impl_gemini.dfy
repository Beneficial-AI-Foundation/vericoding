// <vc-preamble>
function Power(base: int, exp: nat): int
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): [Prove that Power(4, m) is always positive] */
lemma LemmaPowerIsPositive(m: nat)
    ensures Power(4, m) > 0
    decreases m
{
    if m > 0 {
        LemmaPowerIsPositive(m - 1);
    }
}

/* helper modified by LLM (iteration 4): [Prove multiplicative property of Power] */
lemma LemmaPowerProduct(m: nat, k: nat)
    requires m >= k
    ensures Power(4, m) == Power(4, k) * Power(4, m - k)
    decreases m - k
{
    if m > k {
        LemmaPowerProduct(m - 1, k);
    }
}

/* helper modified by LLM (iteration 4): [Prove that if n > 0 and n is a power of 4, it's divisible by 4] */
lemma LemmaPowerDivisibleBy4(m: nat)
    requires m > 0
    ensures Power(4, m) % 4 == 0
{
    assert Power(4, m) == 4 * Power(4, m - 1);
}

/* helper modified by LLM (iteration 4): [Lemma to prove contradiction when a number is not a power of four] */
lemma LemmaNonPowerOfFour(temp_n: nat, k: nat)
    requires temp_n > 1
    requires temp_n % 4 != 0
    ensures forall m: nat :: temp_n * Power(4, k) != Power(4, m)
{
    forall m: nat ensures temp_n * Power(4, k) != Power(4, m) {
        if temp_n * Power(4, k) == Power(4, m) {
            LemmaPowerIsPositive(k);
            if m >= k {
                LemmaPowerProduct(m, k);
                var diff := m-k;
                assert temp_n == Power(4, diff);
                if diff == 0 {
                    assert temp_n == 1; // Contradicts temp_n > 1
                } else { // diff > 0
                    LemmaPowerDivisibleBy4(diff);
                    assert temp_n % 4 == 0; // Contradicts temp_n % 4 != 0
                }
            } else { // m < k
                LemmaPowerProduct(k, m);
                LemmaPowerIsPositive(m);
                var diff := k - m;
                assert diff >= 1;
                assert temp_n * Power(4, diff) == 1;
                LemmaPowerIsPositive(diff - 1);
                assert Power(4, diff - 1) >= 1;
                assert Power(4, diff) >= 4;
                assert temp_n * Power(4, diff) >= 4; // Contradiction with == 1
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method IfPowerOfFour(n: nat) returns (result: bool)
    ensures result <==> (exists m: nat :: n == Power(4, m))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): [use division with ghost state and helper lemmas] */
    if n == 0 {
        result := false;
        forall m: nat ensures Power(4, m) != 0 { LemmaPowerIsPositive(m); }
        return;
    }

    var temp_n := n;
    ghost var k: nat := 0;

    while temp_n % 4 == 0 && temp_n > 1
        invariant n == temp_n * Power(4, k)
        invariant temp_n > 0
        decreases temp_n
    {
        temp_n := temp_n / 4;
        k := k + 1;
        assert Power(4, k) == 4 * Power(4, k-1); // Aid invariant proof
    }

    if temp_n == 1 {
        result := true;
        assert n == Power(4, k); 
    } else {
        result := false;
        assert temp_n > 1 && temp_n % 4 != 0;
        LemmaNonPowerOfFour(temp_n, k);
        assert forall m: nat :: n != Power(4, m);
    }
}
// </vc-code>
