use vstd::prelude::*;

verus! {

spec fn insert_precond(oline: Seq<char>, l: nat, nl: Seq<char>, p: nat, at_pos: nat) -> bool {
    l <= oline.len() &&
    p <= nl.len() &&
    at_pos <= l
}

spec fn insert_postcond(oline: Seq<char>, l: nat, nl: Seq<char>, p: nat, at_pos: nat, result: Seq<char>) -> bool {
    result.len() == l + p &&
    (forall|i: int| 0 <= i < p ==> #[trigger] result[at_pos + i] == nl[i]) &&
    (forall|i: int| 0 <= i < at_pos ==> #[trigger] result[i] == oline[i]) &&
    (forall|i: int| 0 <= i < l - at_pos ==> #[trigger] result[at_pos + p + i] == oline[at_pos + i])
}

#[verifier::loop_isolation(false)]
fn insert(oline: &Vec<char>, l: usize, nl: &Vec<char>, p: usize, at_pos: usize) -> (result: Vec<char>)
    requires
        insert_precond(oline@, l as nat, nl@, p as nat, at_pos as nat),
        l <= usize::MAX - p,
    ensures
        insert_postcond(oline@, l as nat, nl@, p as nat, at_pos as nat, result@),
{
    let mut result = Vec::with_capacity(l + p);
    
    // Copy characters before insertion point
    let mut i = 0;
    while i < at_pos
        invariant
            i <= at_pos,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == oline@[j],
        /* code modified by LLM (iteration 1): Added decreases clause to ensure loop termination */
        decreases at_pos - i,
    {
        result.push(oline[i]);
        i += 1;
    }
    
    // Insert characters from nl
    let mut j = 0;
    while j < p
        invariant
            j <= p,
            result.len() == at_pos + j,
            forall|k: int| 0 <= k < at_pos ==> #[trigger] result@[k] == oline@[k],
            forall|k: int| 0 <= k < j ==> #[trigger] result@[at_pos + k] == nl@[k],
        /* code modified by LLM (iteration 1): Added decreases clause to ensure loop termination */
        decreases p - j,
    {
        result.push(nl[j]);
        j += 1;
    }
    
    // Copy remaining characters from oline
    let mut k = 0;
    while k < l - at_pos
        invariant
            k <= l - at_pos,
            result.len() == at_pos + p + k,
            forall|m: int| 0 <= m < at_pos ==> #[trigger] result@[m] == oline@[m],
            forall|m: int| 0 <= m < p ==> #[trigger] result@[at_pos + m] == nl@[m],
            forall|m: int| 0 <= m < k ==> #[trigger] result@[at_pos + p + m] == oline@[at_pos + m],
        /* code modified by LLM (iteration 1): Added decreases clause to ensure loop termination */
        decreases (l - at_pos) - k,
    {
        result.push(oline[at_pos + k]);
        k += 1;
    }
    
    result
}

// This proof function corresponds to the theorem insert_spec_satisfied in Lean
// It establishes that any result satisfying the preconditions will satisfy the postcondition
proof fn insert_spec_satisfied(oline: Seq<char>, l: nat, nl: Seq<char>, p: nat, at_pos: nat, result: Seq<char>)
    requires 
        insert_precond(oline, l, nl, p, at_pos),
        // Assume we have a result that satisfies the basic structure requirements
        result.len() == l + p,
        (forall|i: int| 0 <= i < p ==> #[trigger] result[at_pos + i] == nl[i]),
        (forall|i: int| 0 <= i < at_pos ==> #[trigger] result[i] == oline[i]),
        (forall|i: int| 0 <= i < l - at_pos ==> #[trigger] result[at_pos + p + i] == oline[at_pos + i]),
    ensures 
        insert_postcond(oline, l, nl, p, at_pos, result),
{
    // The postcondition follows directly from the requirements
}

fn main() {
    let oline = vec!['h', 'e', 'l', 'l', 'o'];
    let nl = vec!['x', 'y'];
    let result = insert(&oline, 5, &nl, 2, 2);
    /* code modified by LLM (iteration 1): Removed println! statement as it's not supported in Verus */
    // println!("Result: {:?}", result); // Should print ['h', 'e', 'x', 'y', 'l', 'l', 'o']
}

}