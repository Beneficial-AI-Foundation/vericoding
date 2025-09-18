// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute offset modulo n as a usize */
proof fn offset_mod_usize(offset: int, n: usize) -> (result: usize)
    requires
        offset >= 0,
        n > 0,
    ensures
        result < n,
{
    let r = (offset as usize) % n;
    let result = r;
    proof {
        assert(result < n);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn rotate(a: &Vec<i32>, offset: int) -> (result: Vec<i32>)
    requires offset >= 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let src_idx = (i + offset) % (a.len() as int);
            #[trigger] result[i] == a[src_idx]
        },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): rotate using usize arithmetic and offset_mod_usize helper */
    let n = a.len();
    if n == 0 {
        return Vec::new();
    }
    let offset_usize = offset_mod_usize(offset, n);
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
        decreases n - i
    {
        let src_idx = (i + offset_usize) % n;
        let v = a[src_idx];
        res.push(v);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}