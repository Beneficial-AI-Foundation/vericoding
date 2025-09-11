use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn count(a: Vec<String>, sub: Vec<String>, start: Vec<i32>, end_pos: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == sub.len(),
        a.len() == start.len(),
        a.len() == end_pos.len(),
        forall|i: int| 0 <= i < a.len() ==> start[i] <= end_pos[i],
        forall|i: int| 0 <= i < a.len() ==> 0 <= start[i] && start[i] <= a[i]@.len(),
        forall|i: int| 0 <= i < a.len() ==> 0 <= end_pos[i] && end_pos[i] <= a[i]@.len(),
        forall|i: int| 0 <= i < a.len() ==> sub[i]@.len() > 0,
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> 
            (sub[i]@.len() > (end_pos[i] - start[i]) ==> result[i] == 0)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}