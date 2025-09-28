// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn string_to_upper(s: Seq<char>) -> Seq<char> {
    s
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no helpers needed */
// </vc-helpers>

// <vc-spec>
fn upper(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() as int ==>
            result@[i]@ == string_to_upper(a@[i]@) &&
            result@[i]@.len() == a@[i]@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fixed move error by cloning strings */
{
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            result.len() == i as nat,
            forall |j: int| 0 <= j < i as int ==>
                result@[j]@ == string_to_upper(a@[j]@) &&
                result@[j]@.len() == a@[j]@.len(),
            i <= a.len()
        decreases a.len() - i
    {
        result.push(a[i].clone());
        i = i + 1;
    }
    proof {
        let len = a.len() as int;
        let len_nat = a.len();
        assert(len == i as int);
        assert forall |k: int| 0 <= k < len implies
            result@[k]@ == string_to_upper(a@[k]@) &&
            result@[k]@.len() == a@[k]@.len() by {
            assert(k < i as int);
        }
    }
    result
}
// </vc-code>


}
fn main() {}