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
    let final_result = first_part.add(second);
    
    // Proof assertions to help verification
    assert(final_result.len() == first_part.len() + second.len());
    assert(first_part.len() == first.len() - 1);
    assert(final_result.len() == first.len() - 1 + second.len());
    
    // Prove the first part matches
    assert forall|i: int| 0 <= i < first.len() - 1 implies final_result.spec_index(i) == first.spec_index(i) by {
        assert(i < first_part.len());
        assert(final_result.spec_index(i) == first_part.spec_index(i));
        assert(first_part.spec_index(i) == first.spec_index(i));
    };
    
    // Prove the second part matches
    assert forall|i: int| first.len() - 1 <= i < final_result.len() implies final_result.spec_index(i) == second.spec_index(i - (first.len() - 1)) by {
        let second_index = i - (first.len() - 1);
        assert(i >= first_part.len());
        assert(second_index >= 0);
        assert(second_index < second.len());
        assert(final_result.spec_index(i) == second.spec_index(second_index));
    };
    
    final_result
}

}