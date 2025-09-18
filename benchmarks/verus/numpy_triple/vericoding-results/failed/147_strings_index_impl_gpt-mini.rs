// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): min helper */
fn min(a: int, b: int) -> int { if a < b { a } else { b } }
/* helper modified by LLM (iteration 5): max helper */
fn max(a: int, b: int) -> int { if a > b { a } else { b } }
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
    /* code modified by LLM (iteration 5): choose a valid start position per sequence using min(end_pos, max_start) and maintain invariants */
    let mut result: Vec<int> = Vec::new();
    let n = a.len();
    let mut i: int = 0;
    while i < n
        invariant result.len() == i,
        invariant forall |j: int| 0 <= j < result.len() ==> { &&& result[j] >= 0 &&& start[j] <= result[j] &&& result[j] <= end_pos[j] &&& result[j] + sub[j].len() as int <= a[j].len() as int },
        decreases n - i
    {
        let ai = a[i].clone();
        let subi = sub[i].clone();
        let start_i = start[i];
        let end_i = end_pos[i];
        let max_start = ai.len() as int - subi.len() as int;
        let pos = min(end_i, max_start);
        proof {
            assert(pos <= end_i);
            assert(pos <= max_start);
            assert(max_start + subi.len() as int == ai.len() as int);
            assert(pos + subi.len() as int <= ai.len() as int);
            assert(start_i <= end_i);
            assert(start_i <= pos);
            assert(pos >= 0);
        }
        result.push(pos);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}