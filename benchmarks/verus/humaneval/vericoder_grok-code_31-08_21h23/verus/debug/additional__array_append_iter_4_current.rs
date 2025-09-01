use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this fix
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_append(a: Vec<i32>, b: i32) -> (result: Vec<i32>)
    // post-conditions-start
    ensures
        result.len() == a.len() + 1,
        forall|i: int| #![auto] 0 <= i && i < result.len() ==> result[i] == (if i < a.len() { a[i] } else { b }),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    proof {
        // Initial length is 0
        assert(result.len() == 0);
    }
    for i in 0..a.len()
        invariant
            0 <= (i as int) <= a.len() as int,
            result.len() == (i as int),
            forall|j: int| #![auto] 0 <= j && j < (i as int) ==> #[trigger] result@[j] == a@[j]
    {
        proof {
            let old_len = result.len();
        }
        result.push(a[i]);
        proof {
            // After push, length increases by 1
            assert(result.len() == old_len + 1);
        }
    }
    proof {
        // After loop, result has same length as a and same elements
        assert(result.len() == a.len());
        assert(forall|j: int| #![auto] 0 <= j && j < a.len() ==> #[trigger] result@[j] == a@[j]);
    }
    result.push(b);
    proof {
        // Now result has length a.len() + 1, and last element is b
        assert(result.len() == a.len() + 1);
        assert(forall|j: int| #![auto] 0 <= j && j < a.len() ==> #[trigger] result@[j] == a@[j]);
        assert(result@[a.len() as int] == b);
    }
    result
}
// </vc-code>

fn main() {}
}