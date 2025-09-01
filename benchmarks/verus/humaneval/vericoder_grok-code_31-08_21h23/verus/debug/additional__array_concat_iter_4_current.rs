use vstd::prelude::*;

verus! {

// <vc-helpers>
// This section remains unchanged as no helpers are needed for this fix
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_concat(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> result[i] == a[i],
        forall|i: int| 0 <= i && i < b.len() ==> result[i + a.len()] == b[i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i: int = 0;

    let len_a: int = a@.len();
    let len_b: int = b@.len();
    if i < len_a {
        proof { assert(false); } // Unreach due to invariant
    }

    while i < len_a
        invariant
            0 <= i <= len_a,
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]) == a@[j],
        decreases len_a - i
    {
        let idx = i as usize;
        result.push(a[idx]);
        i += 1;

        proof {
            assert(result@.len() == i);
            assert(forall|j: int| 0 <= j < i ==> (#[trigger] result@[j]) == a@[j]);
        }
    }

    proof {
        assert(result@.len() == len_a);
        assert(forall|k: int| 0 <= k < len_a ==> (#[trigger] result@[k]) == a@[k]);
    }

    let mut j: int = 0;

    while j < len_b
        invariant
            0 <= j <= len_b,
            result@.len() == len_a + j,
            forall|k: int| 0 <= k < len_a ==> (#[trigger] result@[k]) == a@[k],
            forall|k: int| 0 <= k < j ==> (#[trigger] result@[k + len_a]) == b@[k],
        decreases len_b - j
    {
        let idx = j as usize;
        result.push(b[idx]);
        j += 1;

        proof {
            assert(result@.len() == len_a + j);
            assert(forall|k: int| 0 <= k < j ==> (#[trigger] result@[k + len_a]) == b@[k]);
        }
    }

    proof {
        assert(forall|ii: int| 0 <= ii < len_a ==> (#[trigger] result@[ii]) == a@[ii]);
        assert(forall|ii: int| 0 <= ii < len_b ==> (#[trigger] result@[ii + len_a]) == b@[ii]);
    }

    result
}
// </vc-code>

fn main() {}
}