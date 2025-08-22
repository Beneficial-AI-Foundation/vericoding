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
        let mut rest = l2.clone();
        rest.remove(0);
        if digit < 10 {
            let mut result = vec![digit];
            let tail = add_aux(Vec::new(), rest, 0);
            result.append(&mut tail.clone());
            result
        } else {
            let mut result = vec![digit - 10];
            let tail = add_aux(Vec::new(), rest, 1);
            result.append(&mut tail.clone());
            result
        }
    } else if l2.len() == 0 {
        let digit = l1[0] + carry;
        let mut rest = l1.clone();
        rest.remove(0);
        if digit < 10 {
            let mut result = vec![digit];
            let tail = add_aux(rest, Vec::new(), 0);
            result.append(&mut tail.clone());
            result
        } else {
            let mut result = vec![digit - 10];
            let tail = add_aux(rest, Vec::new(), 1);
            result.append(&mut tail.clone());
            result
        }
    } else {
        let digit = l1[0] + l2[0] + carry;
        let mut rest1 = l1.clone();
        let mut rest2 = l2.clone();
        rest1.remove(0);
        rest2.remove(0);
        if digit < 10 {
            let mut result = vec![digit];
            let tail = add_aux(rest1, rest2, 0);
            result.append(&mut tail.clone());
            result
        } else {
            let mut result = vec![digit - 10];
            let tail = add_aux(rest1, rest2, 1);
            result.append(&mut tail.clone());
            result
        }
    }
}

// Main function
fn add_two_numbers(l1: Vec<u32>, l2: Vec<u32>) -> (result: Vec<u32>)
    requires add_two_numbers_precond(l1@, l2@)
    ensures add_two_numbers_postcond(l1@, l2@, result@)
{
    // Reverse the input vectors to process from least significant digit
    let mut rev1 = l1.clone();
    let mut rev2 = l2.clone();
    rev1.reverse();
    rev2.reverse();
    
    // Perform addition
    let mut sum = add_aux(rev1, rev2, 0);
    
    // Remove leading zeros and reverse back
    while sum.len() > 1 && sum[sum.len() - 1] == 0 {
        sum.pop();
    }
    
    // Handle the case where the result is zero
    if sum.len() == 0 {
        sum.push(0);
    }
    
    sum.reverse();
    sum
}

} // verus!

fn main() {
    let l1 = vec![2, 4, 3];
    let l2 = vec![5, 6, 4];
    let result = add_two_numbers(l1, l2);
    println!("Result: {:?}", result);
}