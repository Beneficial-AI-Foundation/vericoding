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
/* code modified by LLM (iteration 5): Fixed precondition by using conditional access to avoid out of bound; added assert for overflow check in add case */
    let len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::with_capacity(len);
    let mut i = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                if j < c1.len() && j < c2.len() {
                    result@[j] == (c1@[j] + c2@[j]) as int
                } else if j < c1.len() && j >= c2.len() {
                    result@[j] == c1@[j] as int
                } else if j >= c1.len() && j < c2.len() {
                    result@[j] == c2@[j] as int
                } else {
                    result@[j] == 0
                }
            },
        decreases len - i
    {
        let add1 = if i < c1.len() { c1[i] as i32 } else { 0 };
        let add2 = if i < c2.len() { c2[i] as i32 } else { 0 };
        let val_i32 = add1 + add2;
        proof {
            if i < c1.len() && i < c2.len() {
                assert(-128 <= (c1@[i as int] + c2@[i as int]) as int <= 127);
            }
        }
        result.push(val_i32 as i8);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}