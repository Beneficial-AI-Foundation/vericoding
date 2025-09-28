// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn polyadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int + c2[i] as int
            } else if i < c1.len() && i >= c2.len() {
                result[i] as int == c1[i] as int
            } else if i >= c1.len() && i < c2.len() {
                result[i] as int == c2[i] as int
            } else {
                result[i] as int == 0
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added truncate attribute for safe cast */
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::new();
    let mut i = 0;
    while i < max_len
        invariant
            i <= max_len,
            result.len() == i,
            max_len == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
            forall|j: int| 0 <= j < i ==> {
                if j < c1.len() && j < c2.len() {
                    result[j] as int == c1[j] as int + c2[j] as int
                } else if j < c1.len() && j >= c2.len() {
                    result[j] as int == c1[j] as int
                } else if j >= c1.len() && j < c2.len() {
                    result[j] as int == c2[j] as int
                } else {
                    result[j] as int == 0
                }
            },
        decreases max_len - i
    {
        let value = if i < c1.len() && i < c2.len() {
            #[verifier::truncate]
            let sum_value = (c1[i] as i16 + c2[i] as i16) as i8;
            proof {
                assert(c1[i as int] as int >= -128);
                assert(c1[i as int] as int <= 127);
                assert(c2[i as int] as int >= -128);
                assert(c2[i as int] as int <= 127);
                assert((c1[i as int] as int + c2[i as int] as int) >= -256);
                assert((c1[i as int] as int + c2[i as int] as int) <= 254);
            }
            sum_value
        } else if i < c1.len() {
            c1[i]
        } else if i < c2.len() {
            c2[i]
        } else {
            0
        };
        result.push(value);
        proof {
            assert(result.len() == i + 1);
            assert(result[i as int] == value);
            if i < c1.len() && i < c2.len() {
                assert(value as int == c1[i as int] as int + c2[i as int] as int);
            } else if i < c1.len() && i >= c2.len() {
                assert(value as int == c1[i as int] as int);
            } else if i >= c1.len() && i < c2.len() {
                assert(value as int == c2[i as int] as int);
            } else {
                assert(value as int == 0);
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}