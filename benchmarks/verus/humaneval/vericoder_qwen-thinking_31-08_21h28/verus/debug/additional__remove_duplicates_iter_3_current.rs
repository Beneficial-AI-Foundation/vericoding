use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
fn contains(v: &Vec<i32>, x: i32) -> bool {
    for i in 0..v.len() {
        if v[i] == x {
            return true;
        }
    }
    false
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        a.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    for i in 0..a.len() {
        invariant
            (forall k: int :: #[trigger(result[k])] 0 <= k < result.len() ==> in_array(a@, result[k])) &&
            (forall k: int, m: int :: #[trigger(result[k])] 0 <= k < m < result.len() ==> result[k] != result[m])
        if !contains(&result, a[i]) {
            result.push(a[i]);
        }
    }
    result
}
// </vc-code>

fn main() {}
}