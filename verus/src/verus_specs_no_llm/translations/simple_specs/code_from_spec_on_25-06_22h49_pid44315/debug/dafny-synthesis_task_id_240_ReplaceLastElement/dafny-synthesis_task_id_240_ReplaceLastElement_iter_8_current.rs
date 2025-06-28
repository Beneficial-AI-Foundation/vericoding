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
        // i is in bounds for first_part since i < first.len() - 1 == first_part.len()
        assert(i < first_part.len());
        // For concatenation, indices < first_part.len() index into first_part
        assert(final_result.spec_index(i) == first_part.spec_index(i));
        // subseq preserves elements: first_part[i] == first[i] for valid i
        assert(first_part.spec_index(i) == first.spec_index(i));
    };
    
    // Prove the second part of the concatenation matches second
    assert forall|i: int| first.len() - 1 <= i < final_result.len() implies 
        final_result.spec_index(i) == second.spec_index(i - (first.len() - 1)) by {
        let offset = i - (first.len() - 1);
        // i >= first.len() - 1 == first_part.len(), so we're in the second part
        assert(i >= first_part.len());
        // Check bounds for second
        assert(final_result.len() == first_part.len() + second.len());
        assert(i < first_part.len() + second.len());
        assert(offset == i - first_part.len());
        assert(0 <= offset < second.len());
        // For concatenation, indices >= first_part.len() index into second with offset
        assert(final_result.spec_index(i) == second.spec_index(i - first_part.len()));
        assert(i - first_part.len() == offset);
    };
    
    final_result
}

}