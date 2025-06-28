use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ContainsSequence(list: Seq<Seq<int>>, sub: Seq<int>) -> (result: bool)
    ensures
        result <==> (exists i :: 0 <= i < list.len() && sub == list.spec_index(i))
{
    let mut i: usize = 0;
    while i < list.len()
        invariant
            0 <= i <= list.len(),
            forall j: int :: 0 <= j < i ==> sub != list.spec_index(j),
    {
        if sub == list.spec_index(i as int) {
            // We found the subsequence, so the postcondition is satisfied
            assert(exists k :: 0 <= k < list.len() && sub == list.spec_index(k)) by {
                assert(0 <= i < list.len());
                assert(sub == list.spec_index(i as int));
            }
            return true;
        }
        i = i + 1;
    }
    
    // When we reach here, we know:
    // 1. i == list.len() (from loop condition)
    // 2. forall j: int :: 0 <= j < i ==> sub != list.spec_index(j) (from invariant)
    // Therefore: forall j: int :: 0 <= j < list.len() ==> sub != list.spec_index(j)
    // Which means: !(exists j :: 0 <= j < list.len() && sub == list.spec_index(j))
    
    assert(i == list.len());
    assert(forall j: int :: 0 <= j < list.len() ==> sub != list.spec_index(j));
    
    // Help Verus see that the universal quantifier implies the negation of the existential
    assert(!(exists j :: 0 <= j < list.len() && sub == list.spec_index(j))) by {
        // Proof by contradiction
        assume(exists j :: 0 <= j < list.len() && sub == list.spec_index(j));
        let witness_j = choose |j| 0 <= j < list.len() && sub == list.spec_index(j);
        assert(0 <= witness_j < list.len());
        assert(sub == list.spec_index(witness_j));
        assert(sub != list.spec_index(witness_j)); // contradiction from the universal quantifier
        assert(false);
    }
    
    false
}

}