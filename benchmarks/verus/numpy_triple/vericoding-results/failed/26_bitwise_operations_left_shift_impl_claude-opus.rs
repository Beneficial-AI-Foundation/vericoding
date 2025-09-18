// <vc-preamble>
use vstd::prelude::*;
use vstd::arithmetic::power::pow;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fix type annotation and indexing errors */
    let mut result: Vec<i32> = Vec::new();
    let n = x1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == x1.len(),
            n == x2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result[j as int] == x1[j as int] * pow(2, x2[j as int] as nat),
            forall|j: int| 0 <= j < i as int && x2[j as int] == 0 ==> result[j as int] == x1[j as int],
            forall|j: int| 0 <= j < i as int && x1[j as int] == 0 ==> result[j as int] == 0,
            forall|j: int| 0 <= j < i as int && x1[j as int] > 0 && x2[j as int] > 0 ==> result[j as int] > x1[j as int],
            forall|j: int| 0 <= j < i as int && x1[j as int] < 0 && x2[j as int] > 0 ==> result[j as int] < x1[j as int],
        decreases n - i
    {
        let shift_amount = x2[i as int];
        let value = x1[i as int];
        
        if shift_amount == 0 {
            result.push(value);
        } else {
            let mut shifted_value: i32 = value;
            let mut k: i32 = 0;
            while k < shift_amount
                invariant
                    0 <= k <= shift_amount,
                    shift_amount >= 0,
                    shift_amount == x2[i as int],
                    value == x1[i as int],
                    shifted_value as int == value as int * pow(2, k as nat),
                decreases shift_amount - k
            {
                proof {
                    assert(shifted_value as int * 2 == value as int * pow(2, k as nat) * 2);
                    assert(value as int * pow(2, k as nat) * 2 == value as int * pow(2, (k + 1) as nat));
                }
                shifted_value = shifted_value << 1;
                k = k + 1;
            }
            assert(shifted_value as int == value as int * pow(2, shift_amount as nat));
            assert(shifted_value as int == x1[i as int] as int * pow(2, x2[i as int] as nat));
            result.push(shifted_value);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}