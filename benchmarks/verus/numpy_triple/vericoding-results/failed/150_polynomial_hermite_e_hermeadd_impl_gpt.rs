// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): spec accessor for coefficient with default 0 */
spec fn coeff_at(v: Seq<i8>, i: int) -> int {
    if 0 <= i && i < v.len() { v[i] as int } else { 0 }
}

/* helper modified by LLM (iteration 2): spec clamp from int to i8 to reason about bounds */
spec fn clamp_to_i8(n: int) -> i8 {
    if n < -128 { -128i8 } else if n > 127 { 127i8 } else { n as i8 }
}
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
    /* code modified by LLM (iteration 2): avoid using ghost int variables in exec code; compute with i16 and clamp to i8 inline */
    let l1 = c1.len();
    let l2 = c2.len();
    let lm = if l1 >= l2 { l1 } else { l2 };

    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < lm
        invariant
            res.len() == i,
            i <= lm,
            forall|j: int| 0 <= j < i as int ==> {
                let coeff1 = if j < c1@.len() { c1@[j] as int } else { 0 };
                let coeff2 = if j < c2@.len() { c2@[j] as int } else { 0 };
                res@[j] as int == coeff1 + coeff2
            },
        decreases lm - i,
    {
        let v1: i8 = if i < l1 { c1[i] } else { 0i8 };
        let v2: i8 = if i < l2 { c2[i] } else { 0i8 };
        let v1i16: i16 = v1 as i16;
        let v2i16: i16 = v2 as i16;
        let sum: i16 = v1i16 + v2i16;
        let x: i8 = if sum < -128i16 { -128i8 } else if sum > 127i16 { 127i8 } else { sum as i8 };
        res.push(x);
        i = i + 1;
    }

    res
}
// </vc-code>

}
fn main() {}