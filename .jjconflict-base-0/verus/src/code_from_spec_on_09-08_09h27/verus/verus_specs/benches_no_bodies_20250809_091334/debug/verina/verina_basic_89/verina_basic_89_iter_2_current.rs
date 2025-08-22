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
    /* code modified by LLM (iteration 1): Fixed Vec::from_seq to use proper conversion from sequence to vector */
    let v = Vec::<int>::new();
    let mut result_v = v;
    let mut i = 0;
    while i < s.len()
        invariant 0 <= i <= s.len(), result_v@.len() == i, 
                  forall|j: int| 0 <= j < i ==> result_v@[j] == s[j]
        decreases s.len() - i
    {
        result_v.push(s[i]);
        i = i + 1;
    }
    set_to_seq(result_v)@
}

// Theorem stating the function satisfies its specification
proof fn set_to_seq_spec_satisfied(s: Seq<int>)
    requires set_to_seq_precond(s),
    ensures set_to_seq_postcond(s, set_to_seq_spec(s))
{
    /* code modified by LLM (iteration 1): Fixed Vec::from_seq usage in proof function */
    let v = Vec::<int>::new();
    let mut result_v = v;
    let mut i = 0;
    while i < s.len()
        invariant 0 <= i <= s.len(), result_v@.len() == i,
                  forall|j: int| 0 <= j < i ==> result_v@[j] == s[j]
        decreases s.len() - i
    {
        result_v.push(s[i]);
        i = i + 1;
    }
    let result = set_to_seq(result_v);
    assert(set_to_seq_postcond(s, result@));
}

fn main() {
    /* code modified by LLM (iteration 1): Fixed integer types and debug printing */
    let test_vec = vec![1int, 2int, 2int, 3int, 1int, 4int, 3int];
    let result = set_to_seq(test_vec);
    // Convert to regular integers for printing
    let printable_result: Vec<i32> = result.iter().map(|&x| x as i32).collect();
    println!("Result: {:?}", printable_result);
}

}