// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): provide a spec helper to express i8 sums as mathematical ints without risking overflow */
spec fn sum_i8_as_int(a: i8, b: i8) -> int {
    a as int + b as int
}
// </vc-helpers>

// <vc-spec>
fn add(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == x1[i] as int + x2[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix trigger syntax and decreases measure; perform element-wise addition with invariant over prefix */
    let n: usize = x1.len();
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i as int <= n as int,
            res.len() == i,
            x1.len() == n,
            x2.len() == n,
            forall|j: int| 0 <= j < i as int ==> #[trigger] res@[j] as int == x1@[j] as int + x2@[j] as int,
        decreases n as int - i as int
    {
        let v: i8 = x1[i] + x2[i];
        res.push(v);
        proof {
            let j = i as int;
            assert(0 <= j && j < res.len() as int);
            assert(res@[j] == v);
            assert(res@[j] as int == x1@[j] as int + x2@[j] as int);
        }
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}