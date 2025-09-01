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
    let mut i: usize = 0;
    let len_a: usize = a.len();
    let len_b: usize = b.len();
    let ghost len_a_int = a@.len();
    let ghost len_b_int = b@.len();

    while i < len_a
        invariant
            (i as int) <= len_a_int,
            result@.len() == (i as int),
            forall|j: int| 0 <= j < (i as int) ==> (#[trigger] result@[j]) == a@[j],
        decreases (len_a as int) - (i as int)
    {
        result.push(a[i]);
        i += 1;

        proof {
            assert(result@.len() == (i as int));
            assert(forall|j: int| 0 <= j < (i as int) ==> (#[trigger] result@[j]) == a@[j]);
        }
    }

    proof {
        assert(result@.len() == len_a_int);
        assert(forall|k: int| 0 <= k < len_a_int ==> (#[trigger] result@[k]) == a@[k]);
    }

    let mut j: usize = 0;

    while j < len_b
        invariant
            (j as int) <= len_b_int,
            result@.len() == len_a_int + (j as int),
            forall|k: int| 0 <= k < len_a_int ==> (#[trigger] result@[k]) == a@[k],
            forall|k: int| 0 <= k < (j as int) ==> (#[trigger] result@[k + len_a_int]) == b@[k],
        decreases (len_b as int) - (j as int)
    {
        result.push(b[j]);
        j += 1;

        proof {
            assert(result@.len() == len_a_int + (j as int));
            assert(forall|k: int| 0 <= k < (j as int) ==> (#[trigger] result@[k + len_a_int]) == b@[k]);
        }
    }

    proof {
        assert(forall|ii: int| 0 <= ii < len_a_int ==> (#[trigger] result@[ii]) == a@[ii]);
        assert(forall|ii: int| 0 <= ii < len_b_int ==> (#[trigger] result@[ii + len_a_int]) == b@[ii]);
    }

    result
}
// </vc-code>

fn main() {}
}