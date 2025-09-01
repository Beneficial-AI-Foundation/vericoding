use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn concat_spec(a: Seq<i32>, b: Seq<i32>) -> Seq<i32> {
    a + b
}

proof fn lemma_concat_properties(a: Seq<i32>, b: Seq<i32>)
    ensures
        concat_spec(a, b).len() == a.len() + b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> concat_spec(a, b)[i] == a[i],
        forall|i: int| 0 <= i && i < b.len() ==> concat_spec(a, b)[i + a.len()] == b[i],
{
    assert(concat_spec(a, b) =~= a + b);
    assert forall|i: int| 0 <= i && i < a.len() implies concat_spec(a, b)[i] == a[i] by {
        assert((a + b)[i] == a[i]);
    };
    assert forall|i: int| 0 <= i && i < b.len() implies concat_spec(a, b)[i + a.len()] == b[i] by {
        assert((a + b)[i + a.len()] == b[i]);
    };
}
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
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result@[j] == a@[j],
    {
        result.push(a[i]);
        i += 1;
    }
    let old_len = result.len();
    proof { assert(result@ =~= a@.subrange(0, i as int)); }
    
    let mut j = 0;
    while j < b.len()
        invariant
            0 <= j <= b.len(),
            result.len() == old_len + j,
            forall|k: int| 0 <= k && k < old_len ==> result@[k] == a@[k],
            forall|k: int| 0 <= k && k < j ==> result@[old_len + k] == b@[k],
    {
        result.push(b[j]);
        j += 1;
    }
    proof {
        lemma_concat_properties(a@, b@);
        assert(result@ =~= concat_spec(a@, b@));
    }
    result
}
// </vc-code>

fn main() {}
}