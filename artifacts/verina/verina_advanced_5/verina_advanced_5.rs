use vstd::prelude::*;

verus! {

// Convert list of digits to natural number
spec fn list_to_nat(l: Seq<u32>) -> nat
    decreases l.len()
{
    if l.len() == 0 {
        0nat
    } else {
        l[0] as nat + 10nat * list_to_nat(l.subrange(1, l.len() as int))
    }
}

// Precondition for addTwoNumbers
spec fn add_two_numbers_precond(l1: Seq<u32>, l2: Seq<u32>) -> bool {
    l1.len() > 0 && l2.len() > 0 &&
    (forall|i: int| 0 <= i < l1.len() ==> l1[i] < 10) &&
    (forall|i: int| 0 <= i < l2.len() ==> l2[i] < 10) &&
    (l1[l1.len() - 1] != 0 || l1 == seq![0u32]) &&
    (l2[l2.len() - 1] != 0 || l2 == seq![0u32])
}

// Postcondition for addTwoNumbers
spec fn add_two_numbers_postcond(l1: Seq<u32>, l2: Seq<u32>, result: Seq<u32>) -> bool {
    list_to_nat(result) == list_to_nat(l1) + list_to_nat(l2) &&
    (forall|i: int| 0 <= i < result.len() ==> result[i] < 10) &&
    (result.len() == 0 || result[result.len() - 1] != 0 || 
     (l1 == seq![0u32] && l2 == seq![0u32] && result == seq![0u32]))
}

// Helper function for addition with carry
fn add_aux(l1: Vec<u32>, l2: Vec<u32>, carry: u32) -> (result: Vec<u32>)
    requires 
        forall|i: int| 0 <= i < l1.len() ==> l1[i] < 10,
        forall|i: int| 0 <= i < l2.len() ==> l2[i] < 10,
        carry <= 1
    ensures
        forall|i: int| 0 <= i < result.len() ==> result[i] < 10
    decreases l1.len() + l2.len()
{
    if l1.len() == 0 && l2.len() == 0 {
        if carry == 0 {
            vec![]
        } else {
            vec![carry]
        }
    } else if l1.len() > 0 && l2.len() == 0 {
        let h1 = l1[0];
        let mut t1 = l1;
        t1.remove(0);
        let sum = h1 + carry;
        let mut result = add_aux(t1, vec![], sum / 10);
        result.insert(0, sum % 10);
        result
    } else if l1.len() == 0 && l2.len() > 0 {
        let h2 = l2[0];
        let mut t2 = l2;
        t2.remove(0);
        let sum = h2 + carry;
        let mut result = add_aux(vec![], t2, sum / 10);
        result.insert(0, sum % 10);
        result
    } else {
        let h1 = l1[0];
        let h2 = l2[0];
        let mut t1 = l1;
        let mut t2 = l2;
        t1.remove(0);
        t2.remove(0);
        let sum = h1 + h2 + carry;
        let mut result = add_aux(t1, t2, sum / 10);
        result.insert(0, sum % 10);
        result
    }
}

// Main function
fn add_two_numbers(l1: Vec<u32>, l2: Vec<u32>) -> (result: Vec<u32>)
    requires add_two_numbers_precond(l1@, l2@)
    ensures add_two_numbers_postcond(l1@, l2@, result@)
{
    let ghost l1_spec = l1@;
    let ghost l2_spec = l2@;
    let result = add_aux(l1, l2, 0);
    proof {
        // In the original Lean code, the proof was marked as 'sorry'
        // This indicates the proof is not provided and needs to be completed
        assume(add_two_numbers_postcond(l1_spec, l2_spec, result@));
    }
    result
}

} // verus!

fn main() {
    // Empty main function for compilation
}