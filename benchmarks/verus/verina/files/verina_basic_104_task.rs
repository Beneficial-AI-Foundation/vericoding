// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn find_key(entries: Seq<(i32, i32)>, k: i32) -> Option<i32> {
    entries.filter(|p: (i32, i32)| p.0 == k).map(|p: (i32, i32)| p.1).first()
}

fn update_map(m1: &Vec<(i32, i32)>, m2: &Vec<(i32, i32)>) -> (result: Vec<(i32, i32)>)
    ensures
        forall|k: i32, v: i32| m2.contains((k, v)) ==> result.contains((k, v)),
        forall|k: i32, v: i32| m1.contains((k, v)) && !exists|v2: i32| m2.contains((k, v2)) ==> result.contains((k, v)),
        forall|k: i32, v: i32| result.contains((k, v)) ==> 
            (m2.contains((k, v)) || (m1.contains((k, v)) && !exists|v2: i32| m2.contains((k, v2)))),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i].0 <= result[j].0,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}
fn main() {}