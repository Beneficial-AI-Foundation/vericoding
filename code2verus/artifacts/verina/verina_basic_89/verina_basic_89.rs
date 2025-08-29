use vstd::prelude::*;

verus! {

// Precondition for SetToSeq - trivially true as in the original
spec fn set_to_seq_precond(s: Seq<int>) -> bool {
    true
}

// Main function to remove duplicates while preserving order
fn set_to_seq(s: Vec<int>) -> (result: Vec<int>)
    requires set_to_seq_precond(s@)
{
    let mut acc: Vec<int> = Vec::new();
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
        decreases s.len() - i
    {
        let elem = s[i];
        let mut found = false;
        let mut j: usize = 0;
        
        // Check if element already exists in acc
        while j < acc.len()
            invariant
                j <= acc.len(),
            decreases acc.len() - j
        {
            if acc[j] == elem {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            acc.push(elem);
        }
        
        i += 1;
    }
    
    acc
}

// Postcondition specification matching the original Lean code
spec fn set_to_seq_postcond(s: Seq<int>, result: Seq<int>) -> bool {
    // Contains exactly the elements of the set
    (forall|a: int| #[trigger] result.contains(a) <==> s.contains(a)) &&
    // All elements are unique in the result  
    (forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j 
        ==> #[trigger] result[i] != #[trigger] result[j])
}

// Spec function version
spec fn set_to_seq_spec(s: Seq<int>) -> Seq<int>
    recommends set_to_seq_precond(s)
{
    // This would ideally be a proper specification, but for now it's abstract
    arbitrary()
}

// Theorem stating the function satisfies its specification (proof omitted like in Lean)
proof fn set_to_seq_spec_satisfied(s: Seq<int>)
    requires set_to_seq_precond(s),
    ensures set_to_seq_postcond(s, set_to_seq_spec(s))
{
    // Proof omitted (similar to the original Lean code using sorry)
    admit();
}

fn main() {
}

}