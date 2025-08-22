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
            Vec::new()
        } else {
            vec![carry]
        }
    } else if l1.len() == 0 {
        let digit = l2[0] + carry;
        let mut result = vec![digit % 10];
        let new_carry = digit / 10;
        /* code modified by LLM (iteration 1): Fixed subrange call to avoid 'as int' cast in executable code */
        let rest = add_aux(Vec::new(), l2.subrange(1, l2.len()), new_carry);
        result.append(rest);
        result
    } else if l2.len() == 0 {
        let digit = l1[0] + carry;
        let mut result = vec![digit % 10];
        let new_carry = digit / 10;
        /* code modified by LLM (iteration 1): Fixed subrange call to avoid 'as int' cast in executable code */
        let rest = add_aux(l1.subrange(1, l1.len()), Vec::new(), new_carry);
        result.append(rest);
        result
    } else {
        let digit = l1[0] + l2[0] + carry;
        let mut result = vec![digit % 10];
        let new_carry = digit / 10;
        /* code modified by LLM (iteration 1): Fixed subrange calls to avoid 'as int' cast in executable code */
        let rest = add_aux(l1.subrange(1, l1.len()), l2.subrange(1, l2.len()), new_carry);
        result.append(rest);
        result
    }
}

// Main function
fn add_two_numbers(l1: Vec<u32>, l2: Vec<u32>) -> (result: Vec<u32>)
    requires add_two_numbers_precond(l1@, l2@)
    ensures add_two_numbers_postcond(l1@, l2@, result@)
{
    let result = add_aux(l1, l2, 0);
    
    // Handle the special case where result might be empty (shouldn't happen with our preconditions)
    if result.len() == 0 {
        vec![0]
    } else {
        result
    }
}

} // verus!

fn main() {
    let l1 = vec![2, 4, 3];  // represents 342
    let l2 = vec![5, 6, 4];  // represents 465
    let result = add_two_numbers(l1, l2);  // should be [7, 0, 8] representing 807
    println!("Addition result: {:?}", result);
}