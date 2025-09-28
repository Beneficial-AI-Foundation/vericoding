// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum NewAxis {
    Newaxis,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax by adding fn keyword */
fn lemma forall_invariant_preserved(result: Seq<Seq<i8>>, v: Seq<i8>, i: nat)
    requires
        i < v.len(),
        result.len() == i,
        forall|j: int| 0 <= j < i ==> (
            result[j].len() == 1 &&
            result[j][0] == v[j]
        ),
    ensures
        forall|j: int| 0 <= j < i + 1 ==> (
            result.push(seq![v[i as int]])[j].len() == 1 &&
            result.push(seq![v[i as int]])[j][0] == v[j]
        ),
{
    let new_result = result.push(seq![v[i as int]]);
    assert forall|j: int| 0 <= j < i + 1 implies (
        new_result[j].len() == 1 &&
        new_result[j][0] == v[j]
    ) by {
        if j < i {
            assert(new_result[j] == result[j]);
        } else {
            assert(j == i);
            assert(new_result[j] == seq![v[i as int]]);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn expand_to_column(v: Vec<i8>, axis: NewAxis) -> (result: Vec<Vec<i8>>)
    ensures
        result@.len() == v@.len(),
        forall|i: int| 0 <= i < result@.len() ==> (
            result@[i].len() == 1 &&
            result@[i][0] == v@[i]
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using corrected lemma syntax */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut i = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> (
                result@[j].len() == 1 &&
                result@[j][0] == v@[j]
            ),
        decreases v@.len() - i
    {
        let mut inner_vec: Vec<i8> = Vec::new();
        inner_vec.push(v[i]);
        
        proof {
            forall_invariant_preserved(result@, v@, i as nat);
        }
        
        result.push(inner_vec);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}