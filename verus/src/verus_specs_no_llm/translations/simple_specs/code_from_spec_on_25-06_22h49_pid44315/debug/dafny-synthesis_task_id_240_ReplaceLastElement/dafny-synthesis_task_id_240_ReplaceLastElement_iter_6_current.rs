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
    
    // Prove properties about subseq
    assert forall|i: int| 0 <= i < first_part.len() implies first_part.spec_index(i) == first.spec_index(i) by {
        // This follows from the definition of subseq
    };
    
    // Prove the first part of the concatenation matches first
    assert forall|i: int| 0 <= i < first.len() - 1 implies final_result.spec_index(i) == first.spec_index(i) by {
        assert(i < first_part.len());
        // From concatenation properties: final_result[i] == first_part[i] when i < first_part.len()
        assert(final_result.spec_index(i) == first_part.spec_index(i));
        // From subseq properties: first_part[i] == first[i]
        assert(first_part.spec_index(i) == first.spec_index(i));
    };
    
    // Prove the second part of the concatenation matches second
    assert forall|i: int| first.len() - 1 <= i < final_result.len() implies final_result.spec_index(i) == second.spec_index(i - (first.len() - 1)) by {
        let offset = i - (first.len() - 1);
        assert(i >= first_part.len()); // since first_part.len() == first.len() - 1
        assert(0 <= offset < second.len()); // bounds check for second
        // From concatenation properties: final_result[i] == second[i - first_part.len()] when i >= first_part.len()
        assert(final_result.spec_index(i) == second.spec_index(i - first_part.len()));
        assert(i - first_part.len() == offset); // since first_part.len() == first.len() - 1
    };
    
    final_result
}

}