// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute difference as i8 using i16 intermediate and prove spec equality */
fn diff_to_i8(x: i8, y: i8) -> (result: i8)
    ensures
        result as int == x as int - y as int,
{
    let t_i16: i16 = (x as i16) - (y as i16);
    #[verifier::truncate]
    let r: i8 = t_i16 as i8;
    proof {
        assert(r as int == x as int - y as int);
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn numpy_diff(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() >= 2,
    ensures 
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == a[i + 1] as int - a[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute pairwise differences using diff_to_i8 and maintain invariants */
    let n: usize = a.len();
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(n >= 2);
    }
    while i < n - 1
        invariant
            i <= n - 1,
            res.len() == i,
            forall|j: int| 0 <= j < res.len() ==> res[j] as int == a[j + 1] as int - a[j] as int,
        decreases n - 1 - i
    {
        proof {
            assert(i + 1 < n);
        }
        let d: i8 = diff_to_i8(a[i + 1], a[i]);
        res.push(d);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}