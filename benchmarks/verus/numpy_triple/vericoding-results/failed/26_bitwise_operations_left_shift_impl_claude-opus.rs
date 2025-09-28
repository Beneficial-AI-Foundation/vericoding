// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added lemmas for power of 2 properties */
proof fn pow2_zero()
    ensures pow(2, 0nat) == 1
{
}

proof fn pow2_succ(n: nat)
    ensures pow(2, n + 1) == 2 * pow(2, n)
{
}

proof fn left_shift_positive(x: int, n: nat)
    requires x > 0, n > 0,
    ensures x * pow(2, n) > x
{
    assert(pow(2, n) >= 2) by {
        if n == 1 {
            assert(pow(2, 1nat) == 2);
        } else {
            assert(pow(2, n) >= pow(2, 1nat));
        }
    }
}

proof fn left_shift_negative(x: int, n: nat)
    requires x < 0, n > 0,
    ensures x * pow(2, n) < x
{
    assert(pow(2, n) >= 2) by {
        if n == 1 {
            assert(pow(2, 1nat) == 2);
        } else {
            assert(pow(2, n) >= pow(2, 1nat));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn left_shift(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x1[i] * pow(2, x2[i] as nat),
        forall|i: int| 0 <= i < result.len() && x2[i] == 0 ==> result[i] == x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] == 0 ==> result[i] == 0,
        forall|i: int| 0 <= i < result.len() && x1[i] > 0 && x2[i] > 0 ==> result[i] > x1[i],
        forall|i: int| 0 <= i < result.len() && x1[i] < 0 && x2[i] > 0 ==> result[i] < x1[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed invariants and added proof blocks */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> result[j] == x1[j] * pow(2, x2[j] as nat),
            forall|j: int| 0 <= j < x2.len() ==> x2[j] >= 0,
        decreases x1.len() - i
    {
        let val = x1[i] as int;
        let shift = x2[i];
        
        proof {
            pow2_zero();
            assert(pow(2, 0nat) == 1);
        }
        
        let mut shifted: int = val;
        let mut j: i32 = 0;
        
        while j < shift
            invariant
                0 <= j <= shift,
                shift >= 0,
                shifted == val * pow(2, j as nat),
            decreases shift - j
        {
            proof {
                pow2_succ(j as nat);
                assert(pow(2, (j + 1) as nat) == 2 * pow(2, j as nat));
                assert(val * pow(2, (j + 1) as nat) == val * (2 * pow(2, j as nat)));
                assert(val * (2 * pow(2, j as nat)) == 2 * (val * pow(2, j as nat)));
            }
            shifted = shifted * 2;
            j = j + 1;
        }
        
        assert(j == shift);
        assert(shifted == val * pow(2, shift as nat));
        assert(shifted == x1[i] * pow(2, x2[i] as nat));
        
        proof {
            if x2[i] == 0 {
                assert(pow(2, 0nat) == 1);
                assert(shifted == x1[i] * 1);
                assert(shifted == x1[i]);
            }
            if x1[i] == 0 {
                assert(shifted == 0 * pow(2, x2[i] as nat));
                assert(shifted == 0);
            }
            if x1[i] > 0 && x2[i] > 0 {
                left_shift_positive(x1[i] as int, x2[i] as nat);
                assert(shifted > x1[i]);
            }
            if x1[i] < 0 && x2[i] > 0 {
                left_shift_negative(x1[i] as int, x2[i] as nat);
                assert(shifted < x1[i]);
            }
        }
        
        result.push(shifted as i32);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}