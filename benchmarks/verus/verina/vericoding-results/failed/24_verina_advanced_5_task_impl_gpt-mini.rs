// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn list_to_nat(l: Seq<u32>) -> nat
    decreases l.len(),
{
    if l.len() == 0 {
        0nat
    } else {
        l[0] as nat + 10nat * list_to_nat(l.subrange(1, l.len() as int))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): placeholder proof helper for potential auxiliary lemmas */
proof fn helper_dummy() { }
// </vc-helpers>

// <vc-spec>
fn add_two_numbers(l1: &Vec<u32>, l2: &Vec<u32>) -> (result: Vec<u32>)
    requires 
        l1.len() > 0,
        l2.len() > 0,
        forall|i: int| 0 <= i < l1.len() ==> l1[i] < 10,
        forall|i: int| 0 <= i < l2.len() ==> l2[i] < 10,
        (l1[l1.len() - 1] != 0 || l1@ == seq![0u32]) &&
        (l2[l2.len() - 1] != 0 || l2@ == seq![0u32]),
    ensures
        list_to_nat(result@) == list_to_nat(l1@) + list_to_nat(l2@),
        forall|i: int| 0 <= i < result.len() ==> result[i] < 10,
        result[result.len() - 1] != 0 || (l1@ == seq![0u32] && l2@ == seq![0u32] && result@ == seq![0u32]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): compute totals using LSB-first representation and avoid Seq.rev()/pow */
    // Compute numeric values of l1 and l2 (LSB-first digits: l[0] is least significant)
    let mut i: usize = 0usize;
    let mut total1: u128 = 0u128;
    let mut pow1: u128 = 1u128;
    while i < l1.len()
        invariant
            i <= l1.len(),
            (total1 as nat) == list_to_nat(l1@.subrange(0, i as int)),
        decreases l1.len() - i
    {
        total1 = total1 + (l1[i] as u128) * pow1;
        pow1 = pow1 * 10u128;
        i += 1;
    }

    let mut j: usize = 0usize;
    let mut total2: u128 = 0u128;
    let mut pow2: u128 = 1u128;
    while j < l2.len()
        invariant
            j <= l2.len(),
            (total2 as nat) == list_to_nat(l2@.subrange(0, j as int)),
        decreases l2.len() - j
    {
        total2 = total2 + (l2[j] as u128) * pow2;
        pow2 = pow2 * 10u128;
        j += 1;
    }

    // Combine totals in executable domain
    let mut temp: u128 = total1 + total2;

    // Decompose temp into base-10 digits (push least-significant-first into result)
    let mut result: Vec<u32> = Vec::new();
    let mut sum_digits: u128 = 0u128; // executable accumulation matching list_to_nat(result@)
    let mut pow_d: u128 = 1u128; // 10^|result|

    if temp == 0u128 {
        result.push(0u32);
        // sum_digits remains 0, pow_d would become 10 if we wanted to continue
    } else {
        while temp > 0u128
            invariant
                temp >= 0u128,
                ((total1 as nat) + (total2 as nat)) == (temp as nat) * (pow_d as nat) + (sum_digits as nat),
            decreases temp as nat
        {
            let d: u32 = (temp % 10u128) as u32;
            result.push(d);
            sum_digits = sum_digits + (d as u128) * pow_d;
            pow_d = pow_d * 10u128;
            temp = temp / 10u128;
        }
    }

    // Final proof block: use the loop invariant at termination (temp == 0)
    proof {
        let orig_total: nat = (total1 as nat) + (total2 as nat);
        // From the digit-extraction invariant at termination we get sum_digits == orig_total
        assert((sum_digits as nat) == orig_total);
        // sum_digits matches list_to_nat(result@)
        assert((sum_digits as nat) == list_to_nat(result@));
        // Combine to conclude the ensures
        assert(list_to_nat(result@) == orig_total);
    }

    result
}
// </vc-code>

}
fn main() {}