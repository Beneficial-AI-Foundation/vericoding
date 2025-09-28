// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): relate usize indices to int range */
proof fn usize_to_int_index(len: usize, i: usize)
    requires
        i < len,
    ensures
        0 <= (i as int),
        (i as int) < (len as int),
{
    proof {
        assert(0 <= (i as int));
        assert((i as int) < (len as int));
    }
}
// </vc-helpers>

// <vc-spec>
fn add(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == a[i] as int + b[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and push sums with explicit casts */
    let n: usize = a.len();
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
        decreases n - i
    {
        proof {
            usize_to_int_index(n, i);
        }
        let ai: i8 = a[i];
        let bi: i8 = b[i];
        let s: int = ai as int + bi as int;
        #[verifier::truncate]
        let si: i8 = s as i8;
        res.push(si);
        i += 1;
    }
    res
}
// </vc-code>


}
fn main() {}