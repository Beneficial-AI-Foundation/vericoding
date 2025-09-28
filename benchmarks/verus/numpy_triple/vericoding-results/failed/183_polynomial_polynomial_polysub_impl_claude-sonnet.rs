// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added wrapping arithmetic operations to handle i8 overflow */
spec fn valid_i8_range(val: int) -> bool {
    -128 <= val <= 127
}

spec fn can_subtract_i8(a: i8, b: i8) -> bool {
    valid_i8_range(a as int - b as int)
}

spec fn can_negate_i8(a: i8) -> bool {
    valid_i8_range(0 - a as int)
}

spec fn wrapping_sub_i8(a: i8, b: i8) -> i8 {
    let diff = a as int - b as int;
    if diff < -128 {
        (diff + 256) as i8
    } else if diff > 127 {
        (diff - 256) as i8
    } else {
        diff as i8
    }
}

spec fn wrapping_neg_i8(a: i8) -> i8 {
    let neg = 0 - a as int;
    if neg < -128 {
        (neg + 256) as i8
    } else if neg > 127 {
        (neg - 256) as i8
    } else {
        neg as i8
    }
}
// </vc-helpers>

// <vc-spec>
fn polysub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int - c2[i] as int
            } else if i < c1.len() && i >= c2.len() {
                result[i] == c1[i]
            } else if i >= c1.len() && i < c2.len() {
                result[i] as int == 0 - c2[i] as int
            } else {
                result[i] == 0
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use wrapping arithmetic and add overflow proof */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::with_capacity(max_len);
    
    let mut i = 0;
    while i < max_len
        invariant
            i <= max_len,
            max_len == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if j < c1.len() && j < c2.len() {
                    result[j] as int == c1[j] as int - c2[j] as int
                } else if j < c1.len() && j >= c2.len() {
                    result[j] == c1[j]
                } else if j >= c1.len() && j < c2.len() {
                    result[j] as int == 0 - c2[j] as int
                } else {
                    result[j] == 0
                }
            },
        decreases max_len - i
    {
        let val = if i < c1.len() && i < c2.len() {
            proof {
                let diff = c1[i] as int - c2[i] as int;
                assert(-256 < diff < 256);
            }
            c1[i].wrapping_sub(c2[i])
        } else if i < c1.len() && i >= c2.len() {
            c1[i]
        } else if i >= c1.len() && i < c2.len() {
            proof {
                let neg = 0 - c2[i] as int;
                assert(-255 <= neg <= 128);
            }
            (0 as i8).wrapping_sub(c2[i])
        } else {
            0
        };
        
        result.push(val);
        
        proof {
            assert(result.len() == i + 1);
            if i < c1.len() && i < c2.len() {
                assert(val as int == c1[i] as int - c2[i] as int);
            } else if i < c1.len() && i >= c2.len() {
                assert(val == c1[i]);
            } else if i >= c1.len() && i < c2.len() {
                assert(val as int == 0 - c2[i] as int);
            } else {
                assert(val == 0);
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}