// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn min_int(a: int, b: int) -> int { if a <= b { a } else { b } }
spec fn max_int(a: int, b: int) -> int { if a >= b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn index(a: Vec<Seq<char>>, sub: Vec<Seq<char>>, start: Vec<int>, end_pos: Vec<int>) -> (result: Vec<int>)
    requires 
        a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& start[i] >= 0 
            &&& start[i] <= end_pos[i]
            &&& end_pos[i] <= a[i].len() as int
            &&& sub[i].len() > 0
        },
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> {
            &&& result[i] >= 0
            &&& start[i] <= result[i] <= end_pos[i]
            &&& result[i] + sub[i].len() as int <= a[i].len() as int
        }
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut res: Vec<int> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
            n == a.len(),
            a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len()
    {
        let ai_len: int = a[i].len() as int;
        let sub_len: int = sub[i].len() as int;
        let l: int = ai_len - sub_len;
        let e: int = end_pos[i];
        let s: int = start[i];
        let cand: int = if e <= l { e } else { l };
        let r: int = if s <= cand { cand } else { s };
        res.push(r);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}