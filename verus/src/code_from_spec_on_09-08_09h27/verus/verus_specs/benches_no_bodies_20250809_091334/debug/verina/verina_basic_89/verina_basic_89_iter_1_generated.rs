use vstd::prelude::*;

verus! {

// Precondition for SetToSeq - trivially true as in the original
spec fn set_to_seq_precond(s: Seq<int>) -> bool {
    true
}

// Main function to remove duplicates while preserving order
fn set_to_seq(s: Vec<int>) -> (result: Vec<int>)
    requires set_to_seq_precond(s@)
    ensures set_to_seq_postcond(s@, result@)
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant 
            0 <= i <= s.len(),
            // Result contains only elements from the original sequence
            forall|x: int| result@.contains(x) ==> s@.contains(x),
            // All elements in result are unique
            forall|j: int, k: int| 0 <= j < result@.len() && 0 <= k < result@.len() && j != k 
                ==> result@[j] != result@[k],
            // If an element appears in s[0..i] and is not in result, then it appeared earlier in s[0..i]
            forall|idx: int| 0 <= idx < i && s@.contains(s@[idx]) && !result@.contains(s@[idx]) ==>
                exists|earlier: int| 0 <= earlier < idx && s@[earlier] == s@[idx]
    {
        let current = s[i];
        let mut found = false;
        let mut j = 0;
        
        // Check if current element is already in result
        while j < result.len()
            invariant
                0 <= j <= result@.len(),
                found <==> exists|k: int| 0 <= k < j && result@[k] == current,
        {
            if result[j] == current {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            result.push(current);
        }
        
        i += 1;
    }
    
    result
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
    set_to_seq(Vec::from_seq(s))@
}

// Theorem stating the function satisfies its specification
proof fn set_to_seq_spec_satisfied(s: Seq<int>)
    requires set_to_seq_precond(s),
    ensures set_to_seq_postcond(s, set_to_seq_spec(s))
{
    let result = set_to_seq(Vec::from_seq(s));
    assert(set_to_seq_postcond(s, result@));
}

fn main() {
    let test_vec = vec![1, 2, 2, 3, 1, 4, 3];
    let result = set_to_seq(test_vec);
    println!("Result: {:?}", result);
}

}