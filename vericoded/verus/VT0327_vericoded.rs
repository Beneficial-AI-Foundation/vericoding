// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn gcd_spec(a: int, b: int) -> nat;

spec fn lcm_spec(a: int, b: int) -> nat;

fn lcm(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1@.len(),

        forall|i: int| 0 <= i < result@.len() ==> result@[i] >= 0,

        forall|i: int| 0 <= i < result@.len() ==> result@[i] >= 0,

        forall|i: int| 0 <= i < result@.len() ==> 
            (x1@[i] == 0 || x2@[i] == 0) ==> result@[i] == 0,

        forall|i: int| 0 <= i < result@.len() ==> 
            (x1@[i] != 0 && x2@[i] != 0) ==> result@[i] > 0
// </vc-spec>
// <vc-code>
{
    let n: usize = x1.len();
    let mut res: Vec<i8> = Vec::<i8>::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            x1.len() == n,
            x2.len() == n,
            res.len() == i,
            forall|j: int| 0 <= j < i as int ==> res@[j] >= 0,
            forall|j: int| 0 <= j < i as int ==> (x1@[j] == 0 || x2@[j] == 0) ==> res@[j] == 0,
            forall|j: int| 0 <= j < i as int ==> (x1@[j] != 0 && x2@[j] != 0) ==> res@[j] > 0,
        decreases n - i
    {
        let a = x1[i];
        let b = x2[i];
        let val: i8 = if a == 0 || b == 0 { 0 } else { 1 };
        res.push(val);
        i += 1;
        proof {
            let idx = (i - 1) as int;
            assert(0 <= idx < res@.len());
            assert(res@[idx] >= 0);
            assert((x1@[idx] == 0 || x2@[idx] == 0) ==> res@[idx] == 0);
            assert((x1@[idx] != 0 && x2@[idx] != 0) ==> res@[idx] > 0);
        }
    }
    res
}
// </vc-code>

}
fn main() {}