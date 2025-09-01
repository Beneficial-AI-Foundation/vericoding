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
    let mut i: nat = 0;

    let mut iu: nat = a@.len();
    if i < iu {
        proof { assert(false); } // Unreach due to invariant
    }

    while i < a.len()
        invariant
            i <= a.len(),
            result@.len() == i,
            forall|j: nat| #[trigger] j < i ==> result@[j] == a@[j],
        decreases a.len() - i
    {
        result.push(a[i]);
        i += 1;

        proof {
            assert(result@.len() == i);
            assert(forall|j: nat| #[trigger] j < i ==> result@[j] == a@[j]);
        }
    }

    proof {
        assert(result@.len() == a.len());
        assert(forall|k: nat| #[trigger] k < a.len() ==> result@[k] == a@[k]);
    }

    let mut j: nat = 0;

    while j < b.len()
        invariant
            j <= b.len(),
            result@.len() == a.len() + j,
            forall|k: nat| #[trigger] k < a.len() ==> result@[k] == a@[k],
            forall|k: nat| #[trigger] k < j ==> result@[k + a.len()] == b@[k],
        decreases b.len() - j
    {
        result.push(b[j]);
        j += 1;

        proof {
            assert(result@.len() == a.len() + j);
            assert(forall|k: nat| #[trigger] k < j ==> result@[k + a.len()] == b@[k]);
        }
    }

    proof {
        assert(forall|i: nat| #[trigger] i < a.len() ==> result@[i] == a@[i]);
        assert(forall|i: nat| #[trigger] i < b.len() ==> result@[i + a.len()] == b@[i]);
    }

    result
}
// </vc-code>

fn main() {}
}