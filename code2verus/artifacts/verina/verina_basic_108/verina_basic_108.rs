use vstd::prelude::*;

verus! {

// Precondition - trivially true in the original
spec fn below_zero_precond(operations: Seq<i32>) -> bool {
    true
}

// Helper function to build the cumulative sum array
fn build_s(operations: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == operations.len() + 1,
        result[0] == 0,
        forall|i: int| 0 <= i < operations.len() ==> #[trigger] result[i + 1] == result[i].wrapping_add(operations[i]),
{
    let mut s = Vec::new();
    s.push(0i32);
    
    let mut i: usize = 0;
    while i < operations.len()
        invariant
            s.len() == i + 1,
            s[0] == 0,
            forall|j: int| 0 <= j < i ==> #[trigger] s[j + 1] == s[j].wrapping_add(operations[j]),
            i <= operations.len(),
        decreases operations.len() - i,
    {
        let last = s[i];
        s.push(last.wrapping_add(operations[i]));
        i += 1;
    }
    s
}

// Helper function to check if any element is negative
fn check_negative(lst: &Vec<i32>) -> (result: bool)
    ensures
        result <==> exists|i: int| 0 <= i < lst.len() && #[trigger] lst[i] < 0,
{
    let mut i: usize = 0;
    while i < lst.len()
        invariant
            forall|j: int| 0 <= j < i ==> #[trigger] lst[j] >= 0,
            i <= lst.len(),
        decreases lst.len() - i,
    {
        if lst[i] < 0 {
            return true;
        }
        i += 1;
    }
    false
}

// Main function
fn below_zero(operations: &Vec<i32>) -> (result: (Vec<i32>, bool))
    requires
        below_zero_precond(operations@),
    ensures ({
        let (s, has_negative) = result;
        &&& s.len() == operations.len() + 1
        &&& s[0] == 0
        &&& (forall|i: int| 0 <= i < operations.len() ==> #[trigger] s[i + 1] == s[i].wrapping_add(operations[i]))
        &&& (has_negative <==> exists|i: int| 0 <= i < s.len() && #[trigger] s[i] < 0)
    }),
{
    let s = build_s(operations);
    let has_negative = check_negative(&s);
    (s, has_negative)
}

fn main() {}

} // verus!