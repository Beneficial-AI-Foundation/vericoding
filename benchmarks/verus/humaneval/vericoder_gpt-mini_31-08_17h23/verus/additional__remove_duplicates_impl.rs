use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
// <vc-helpers>
proof fn in_array_from_index(a: Seq<i32>, i: int)
    requires 0 <= i && i < a.len()
    ensures in_array(a, a[i])
{
    proof {
    }
}

proof fn exists_index_implies_in_array(a: Seq<i32>, t: int, i: int, x: i32)
    requires 0 <= t && t < i && i <= a.len() && a@[t] == x
    ensures in_array(a@, x)
{
    proof {
        assert(a@[t] == x);
        assert(in_array(a@, x));
    }
}
// </vc-helpers>
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
// <vc-code>
{
    // impl-start
    let mut result: Vec<i32> = Vec::new();
    let mut i: int = 0;
    while i < a.len() as int
        invariant 0 <= i && i <= a.len() as int
        invariant (forall|k: int| 0 <= k < (result.len() as int) ==> in_array(a@, result@[k]))
        invariant (forall|p: int, q: int| 0 <= p < q < (result.len() as int) ==> result@[p] != result@[q])
        invariant (forall|k: int| 0 <= k < (result.len() as int) ==> exists|t: int| 0 <= t < i && a@[t] == result@[k])
    {
        let x: i32 = a[i as usize];
        let mut found: bool = false;
        let mut j: int = 0;
        while j < result.len() as int
            invariant 0 <= j && j <= (result.len() as int)
            invariant ((forall|u: int| 0 <= u < j ==> result@[u] != x)) ==> !found
            invariant (exists|u: int| 0 <= u < j && result@[u] == x) ==> found
        {
            if result[j as usize] == x {
                found = true;
            }
            j += 1;
        }
        if !found {
            result.push(x);
            proof {
                // show the invariant for the newly added element holds for the next loop iteration (i will be incremented)
                let k: int = (result.len() as int) - 1;
                assert(result@[k] == x);
                assert(x == a@[i]);
                assert(exists|t: int| 0 <= t < (i + 1) && a@[t] == result@[k]);
            }
        }
        i += 1;
    }
    result
    // impl-end
}
// </vc-code>
// </vc-code>

fn main() {}
}