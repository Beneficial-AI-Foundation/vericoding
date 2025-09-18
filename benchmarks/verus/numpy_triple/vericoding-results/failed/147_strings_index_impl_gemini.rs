// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 3): Added type annotation for result_vec and used spec indexing (`@`) in invariants. */
    let mut result_vec: Vec<int> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == sub.len() && sub.len() == start.len() && start.len() == end_pos.len(),
            forall|k: int| 0 <= k < a.len() as int ==> {
                &&& start@[k] >= 0
                &&& start@[k] <= end_pos@[k]
                &&& end_pos@[k] <= a@[k].len() as int
                &&& sub@[k].len() > 0
            },
            i <= a.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                &&& result_vec@[j] >= 0 
                &&& start@[j] <= result_vec@[j] <= end_pos@[j]
                &&& result_vec@[j] + sub@[j].len() as int <= a@[j].len() as int
            },
    {
        result_vec.push(start[i]);
        i = i + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}