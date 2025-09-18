// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec function to return string sequence length */
spec fn string_len(s: String) -> nat { s@.len() }
// </vc-helpers>

// <vc-spec>
fn str_len(a: Vec<String>) -> (result: Vec<nat>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            &&& result[i] == a[i]@.len()
            &&& result[i] >= 0
            &&& (a[i]@.len() == 0 <==> a[i]@ == Seq::<char>::empty())
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build vector of string lengths using int index with proper invariants */
    let mut result: Vec<nat> = Vec::new();
    let mut i: int = 0;
    while i < a.len() {
        invariant 0 <= i && i <= a.len();
        invariant result.len() == i;
        invariant forall|j: int| 0 <= j < i ==> {
            result[j] == a[j]@.len()
            && result[j] >= 0
            && (a[j]@.len() == 0 <==> a[j]@ == Seq::<char>::empty())
        };
        decreases a.len() - i;
        let l: nat = a[i]@.len();
        result.push(l);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}