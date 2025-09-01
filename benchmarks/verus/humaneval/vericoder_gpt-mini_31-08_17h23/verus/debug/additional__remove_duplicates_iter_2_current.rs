use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
// No helpers needed for this implementation.
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
    // impl-start
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < a.len() as int {
        invariant 0 <= i && i <= a.len() as int;
        invariant forall|k: int| 0 <= k < result.len() as int ==> in_array(a@, result[k as usize]);
        invariant forall|p: int, q: int| 0 <= p < q < result.len() as int ==> result[p as usize] != result[q as usize];
        invariant forall|k: int| 0 <= k < result.len() as int ==> exists|t: int| 0 <= t < i && a[t as usize] == result[k as usize];
        {
            let x: i32 = a[i as usize];
            let mut found: bool = false;
            let mut j: int = 0;
            while j < result.len() as int {
                invariant 0 <= j && j <= result.len() as int;
                invariant (!found) ==> forall|u: int| 0 <= u < j ==> result[u as usize] != x;
                invariant (found) ==> exists|u: int| 0 <= u < j && result[u as usize] == x;
                {
                    if result[j as usize] == x {
                        found = true;
                    }
                    j += 1;
                }
            }
            if !found {
                result.push(x);
            }
            i += 1;
        }
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}