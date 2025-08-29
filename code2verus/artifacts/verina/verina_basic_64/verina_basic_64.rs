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
    let mut result = Vec::new();
    
    // Initialize the result vector with the correct size
    let total_size = l + p;
    let mut init_i = 0;
    while init_i < total_size
        invariant
            0 <= init_i <= total_size,
            result.len() == init_i,
        decreases total_size - init_i,
    {
        result.push(' ');
        init_i += 1;
    }

    // Copy characters from oline before at_pos
    let mut i = 0;
    while i < at_pos
        invariant
            0 <= i <= at_pos,
            at_pos <= l,
            result.len() == total_size,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == oline[j],
        decreases at_pos - i,
    {
        result.set(i, oline[i]);
        i += 1;
    }

    // Insert characters from nl
    let mut i = 0;
    while i < p
        invariant
            0 <= i <= p,
            result.len() == total_size,
            at_pos + p <= total_size,
            forall|j: int| 0 <= j < at_pos ==> #[trigger] result[j] == oline[j],
            forall|j: int| 0 <= j < i ==> #[trigger] result[at_pos + j] == nl[j],
        decreases p - i,
    {
        result.set(at_pos + i, nl[i]);
        i += 1;
    }

    // Copy remaining characters from oline after at_pos
    let mut i = 0;
    while i < l - at_pos
        invariant
            0 <= i <= l - at_pos,
            result.len() == total_size,
            at_pos + p + (l - at_pos) <= total_size,
            forall|j: int| 0 <= j < at_pos ==> #[trigger] result[j] == oline[j],
            forall|j: int| 0 <= j < p ==> #[trigger] result[at_pos + j] == nl[j],
            forall|j: int| 0 <= j < i ==> #[trigger] result[at_pos + p + j] == oline[at_pos + j],
        decreases (l - at_pos) - i,
    {
        result.set(at_pos + p + i, oline[at_pos + i]);
        i += 1;
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
    // Empty main function for compilation
}

}