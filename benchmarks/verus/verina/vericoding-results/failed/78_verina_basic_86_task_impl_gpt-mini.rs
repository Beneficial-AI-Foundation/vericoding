// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): non-negative modulo for indices */
spec fn safe_mod(i: int, n: int) -> (result: int)
    requires n > 0,
    ensures 0 <= result && result < n
{
    let r = i % n;
    if r < 0 { r + n } else { r }
}

/* helper modified by LLM (iteration 5): executable usize modulo helper */
fn usize_mod_add(i: usize, offset: usize, n: usize) -> usize
    requires n > 0
{
    (i + offset) % n
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
    /* code modified by LLM (iteration 5): rotate vector using usize arithmetic; compute offset modulo n and build result */
    let n = a.len();
    if n == 0 {
        Vec::new()
    } else {
        let off = safe_mod(offset, n as int) as usize;
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                result.len() == i,
                forall|j: int| 0 <= j < (i as int) ==> result[j as usize] == a[((j as usize + off) % n)],
            decreases (n as int - i as int)
        {
            let src = (i + off) % n;
            result.push(a[src]);
            i = i + 1;
        }
        result
    }
}
// </vc-code>

}
fn main() {}