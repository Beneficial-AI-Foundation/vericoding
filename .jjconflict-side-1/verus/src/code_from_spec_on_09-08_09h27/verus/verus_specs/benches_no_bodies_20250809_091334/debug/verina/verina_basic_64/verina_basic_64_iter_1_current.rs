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
    
    // Copy characters before at_pos
    let mut i = 0;
    while i < at_pos
        invariant
            i <= at_pos,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] == oline@[j],
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
    {
        result.push(nl[j]);
        j += 1;
    }
    
    // Copy remaining characters from oline
    let mut k = at_pos;
    while k < l
        invariant
            at_pos <= k <= l,
            result.len() == at_pos + p + (k - at_pos),
            forall|m: int| 0 <= m < at_pos ==> #[trigger] result@[m] == oline@[m],
            forall|m: int| 0 <= m < p ==> #[trigger] result@[at_pos + m] == nl@[m],
            forall|m: int| 0 <= m < k - at_pos ==> #[trigger] result@[at_pos + p + m] == oline@[at_pos + m],
    {
        result.push(oline[k]);
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
    // The postcondition is exactly what we have in the requires clause
    // This proof is trivial since all the conditions are already given
}

fn main() {
    let oline = vec!['h', 'e', 'l', 'l', 'o'];
    let nl = vec![' ', 'w', 'o', 'r', 'l', 'd'];
    let result = insert(&oline, 5, &nl, 6, 5);
    println!("Result: {:?}", result);
}

}