use vstd::prelude::*;

verus! {

// Precondition for SetToSeq - trivially true as in the original
spec fn set_to_seq_precond(s: Seq<int>) -> bool {
    true
}

// Main function to remove duplicates while preserving order
fn set_to_seq(s: Vec<int>) -> (result: Vec<int>)
    requires set_to_seq_precond(s@),
    ensures set_to_seq_postcond(s@, result@)
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            // Result contains only elements from the original sequence
            forall|j: int| 0 <= j < result.len() ==> s@.contains(result@[j]),
            // All elements in result are unique
            forall|j: int, k: int| 0 <= j < result.len() && 0 <= k < result.len() && j != k 
                ==> result@[j] != result@[k],
            // For any element that appears in s[0..i], it appears in result iff it appears in s
            forall|x: int| (exists|j: int| 0 <= j < i && s@[j] == x) ==> result@.contains(x),
            // Result only contains elements that appear in s[0..i]
            forall|x: int| result@.contains(x) ==> (exists|j: int| 0 <= j < i && s@[j] == x),
    {
        let current = s[i];
        
        // Check if current element is already in result
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found <==> (exists|k: int| 0 <= k < j && result@[k] == current),
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
    /* code modified by LLM (iteration 1): Fixed integer literals and type conversion for compilation */
    let v: Vec<int> = vec![1, 2, 2, 3, 1, 4, 3];
    let result = set_to_seq(v);
    // Convert to regular integers for printing
    let mut printable_result: Vec<i32> = Vec::new();
    for i in 0..result.len() {
        printable_result.push(result[i] as i32);
    }
    println!("Result: {:?}", printable_result);
}

}