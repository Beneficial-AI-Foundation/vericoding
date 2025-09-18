// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn divmod_single(x: i32, y: i32) -> (i32, i32)
    requires y != 0
{
    let q = x / y;
    let r = x % y;
    (q, r)
}

/* helper modified by LLM (iteration 5): fixed parameter types to match usage */
proof fn divmod_properties(x: i32, y: i32)
    requires y != 0
    ensures
        x == (x / y) * y + (x % y) &&
        (y > 0 ==> 0 <= x % y && x % y < y) &&
        (y < 0 ==> y < x % y && x % y <= 0)
{}
// </vc-helpers>

// <vc-spec>
fn divmod(x1: Vec<i32>, x2: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures ({
        let (quotient, remainder) = result;
        quotient.len() == x1.len() &&
        remainder.len() == x1.len() &&
        forall|i: int| 0 <= i < x1.len() ==> {
            x1[i] == x2[i] * quotient[i] + remainder[i] &&
            (x2[i] > 0 ==> 0 <= remainder[i] && remainder[i] < x2[i]) &&
            (x2[i] < 0 ==> x2[i] < remainder[i] && remainder[i] <= 0)
        }
    })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed indexing syntax and type conversions */
    let mut quotient: Vec<i32> = Vec::new();
    let mut remainder: Vec<i32> = Vec::new();
    
    for i in 0..x1.len()
        invariant
            quotient.len() == i,
            remainder.len() == i,
            forall|j: int| 0 <= j < i ==> {
                x1@[j] == x2@[j] * quotient@[j] + remainder@[j] &&
                (x2@[j] > 0 ==> 0 <= remainder@[j] && remainder@[j] < x2@[j]) &&
                (x2@[j] < 0 ==> x2@[j] < remainder@[j] && remainder@[j] <= 0)
            }
    {
        proof { divmod_properties(x1[i as int], x2[i as int]); }
        let q = x1[i as int] / x2[i as int];
        let r = x1[i as int] % x2[i as int];
        quotient.push(q);
        remainder.push(r);
    }
    
    (quotient, remainder)
}
// </vc-code>

}
fn main() {}