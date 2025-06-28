use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ReplaceLastElement(first: Seq<int>, second: Seq<int>) -> (result: Seq<int>)
    requires
        first.len() > 0
    ensures
        result.len() == first.len() - 1 + second.len(),
        forall|i: int| 0 <= i < first.len() - 1 ==> result.spec_index(i) == first.spec_index(i),
        forall|i: int| first.len() - 1 <= i < result.len() ==> result.spec_index(i) == second.spec_index(i - (first.len() - 1))
{
    let first_part = first.subseq(0, first.len() - 1);
    let final_result = first_part + second;
    
    // Length proof
    assert(first_part.len() == first.len() - 1);
    assert(final_result.len() == first_part.len() + second.len());
    assert(final_result.len() == first.len() - 1 + second.len());
    
    // Prove the first part of the concatenation matches first
    assert forall|i: int| 0 <= i < first.len() - 1 implies 
        final_result.spec_index(i) == first.spec_index(i) by {
        // Establish that i is valid for first_part
        assert(0 <= i < first_part.len());
        // Use the property of concatenation for the first part
        assert(final_result.spec_index(i) == first_part.spec_index(i));
        // Use the property of subseq
        assert(first_part.spec_index(i) == first.spec_index(0 + i));
    };
    
    // Prove the second part of the concatenation matches second
    assert forall|i: int| first.len() - 1 <= i < final_result.len() implies 
        final_result.spec_index(i) == second.spec_index(i - (first.len() - 1)) by {
        // Establish bounds
        assert(i >= first_part.len());
        assert(i < first_part.len() + second.len());
        
        let second_index = i - first_part.len();
        assert(second_index >= 0);
        assert(second_index < second.len());
        
        // Use concatenation property for the second part
        assert(final_result.spec_index(i) == second.spec_index(second_index));
        
        // Show that second_index equals i - (first.len() - 1)
        assert(first_part.len() == first.len() - 1);
        assert(second_index == i - (first.len() - 1));
    };
    
    final_result
}

}