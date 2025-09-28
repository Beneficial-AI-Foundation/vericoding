// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): usize-based min helper */
fn min_usize(a: usize, b: usize) -> usize { if a <= b { a } else { b } }

/* helper modified by LLM (iteration 5): usize-based clamp helper */
fn clamp_usize(x: usize, lo: usize, hi: usize) -> usize { if x < lo { lo } else if x > hi { hi } else { x } }
// </vc-helpers>

// <vc-spec>
fn index(a: Vec<Seq<char>>, sub: Vec<Seq<char>>, start: Vec<i8>, end_pos: Vec<i8>) -> (result: Vec<i8>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& start[i] as int >= 0 
            &&& start[i] as int <= end_pos[i] as int
            &&& end_pos[i] as int <= a[i].len() as int
            &&& sub[i].len() > 0
        },
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& result[i] as int >= 0
            &&& start[i] as int <= result[i] as int <= end_pos[i] as int
            &&& result[i] as int + sub[i].len() as int <= a[i].len() as int
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute chosen index as min(end_pos, a_len - sub_len) using usize and cast to i8 */
    let mut res: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            res.len() == i,
        decreases
            a.len() - i
    {
        let a_len = a[i].len();
        let s = start[i] as usize;
        let e = end_pos[i] as usize;
        let sub_len = sub[i].len();
        let allowed = if a_len >= sub_len { a_len - sub_len } else { 0 };
        let chosen = if allowed < s {
            s
        } else {
            min_usize(e, allowed)
        };
        res.push(chosen as i8);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}