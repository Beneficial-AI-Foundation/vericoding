// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let coeff1 = if i < c1@.len() { c1@[i] as int } else { 0 };
            let coeff2 = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed problematic invariant and proved non-overflow inside loop */
    let c1_seq = c1@;
    let c2_seq = c2@;
    let len1 = c1_seq.len();
    let len2 = c2_seq.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };

    let mut result: Vec<i8> = Vec::with_capacity(max_len);
    let mut i: usize = 0;

    while i < max_len
        invariant
            0 <= i <= max_len,
            c1@.ext_equal(c1_seq),
            c2@.ext_equal(c2_seq),
            len1 == c1_seq.len(),
            len2 == c2_seq.len(),
            max_len == if len1 >= len2 { len1 } else { len2 },
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let coeff1 = if j < c1_seq.len() { c1_seq[j] as int } else { 0 };
                let coeff2 = if j < c2_seq.len() { c2_seq[j] as int } else { 0 };
                #[trigger] result@[j] as int == coeff1 + coeff2
            },
        decreases max_len - i
    {
        let val1 = if i < len1 { c1[i] } else { 0i8 };
        let val2 = if i < len2 { c2[i] } else { 0i8 };

        proof {
            let i_int = i as int;
            let coeff1 = if i_int < len1 { c1_seq[i_int] as int } else { 0 };
            let coeff2 = if i_int < len2 { c2_seq[i_int] as int } else { 0 };
            assert(val1 as int == coeff1);
            assert(val2 as int == coeff2);
            assert(exists|r: i8| r as int == coeff1 + coeff2);
        }

        let sum = val1 + val2;
        result.push(sum);

        i = i + 1;
    }
    result
}

// </vc-code>

}
fn main() {}