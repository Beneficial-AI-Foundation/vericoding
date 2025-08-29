use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_max_element_in_list<T>(v: Vec<T>, max_val: T, max_idx: nat)
    requires
        v.len() > 0,
        max_idx < v.len(),
        max_val == v@[max_idx as int],
        forall|i: int| 0 <= i < v.len() ==> v@[i] <= max_val
    ensures
        forall|i: int| 0 <= i < v.len() ==> v@[i] <= max_val
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: "def max_element(l: list)"
docstring: |
Return maximum element in the list.
test_cases:
- input: [1, 2, 3]
output: 3
- input: [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
output: 123
*/
// </vc-description>

// <vc-spec>
fn max_element(l: Vec<i32>) -> (result: i32)
    requires l.len() > 0,
    ensures exists|i: int| 0 <= i < l.len() && result == l@[i],
    ensures forall|i: int| 0 <= i < l.len() ==> l@[i] <= result
// </vc-spec>

// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed syntax by adding missing commas between ensures clauses in spec */
    let mut max_val = l[0];
    let mut i = 1;
    
    while i < l.len()
        invariant
            0 < i <= l.len(),
            exists|j: int| 0 <= j < i && max_val == l@[j],
            forall|j: int| 0 <= j < i ==> l@[j] <= max_val
    {
        if l[i] > max_val {
            max_val = l[i];
        }
        i += 1;
    }
    
    max_val
}
// </vc-code>

}
fn main() {}