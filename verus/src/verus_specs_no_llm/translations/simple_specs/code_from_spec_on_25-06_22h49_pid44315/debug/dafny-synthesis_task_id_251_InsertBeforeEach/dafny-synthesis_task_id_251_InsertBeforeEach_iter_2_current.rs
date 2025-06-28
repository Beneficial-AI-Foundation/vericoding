use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn InsertBeforeEach(s: Seq<int>, x: int) -> (v: Seq<int>)
    ensures
        v.len() == 2 * s.len(),
        forall |i: int| 0 <= i < s.len() ==> v.spec_index(2*i) == x && v.spec_index(2*i + 1) == s.spec_index(i)
{
    InsertBeforeEachHelper(s, x, 0)
}

fn InsertBeforeEachHelper(s: Seq<int>, x: int, index: usize) -> (v: Seq<int>)
    requires
        index <= s.len()
    ensures
        v.len() == 2 * (s.len() - index),
        forall |i: int| 0 <= i < (s.len() - index) ==> 
            v.spec_index(2*i) == x && v.spec_index(2*i + 1) == s.spec_index(index + i)
    decreases s.len() - index
{
    if index >= s.len() {
        Seq::empty()
    } else {
        let rest = InsertBeforeEachHelper(s, x, index + 1);
        let pair = seq![x, s[index as int]];
        
        // Proof assertions to help verification
        assert(pair.len() == 2);
        assert(pair[0] == x);
        assert(pair[1] == s[index as int]);
        
        let result = pair + rest;
        
        // Prove the postcondition
        assert(result.len() == 2 + rest.len());
        assert(result.len() == 2 + 2 * (s.len() - (index + 1)));
        assert(result.len() == 2 * (s.len() - index));
        
        // Prove the indexing properties
        assert forall |i: int| 0 <= i < (s.len() - index) implies 
            result.spec_index(2*i) == x && result.spec_index(2*i + 1) == s.spec_index(index + i)
        by {
            if i == 0 {
                assert(result.spec_index(0) == pair.spec_index(0));
                assert(result.spec_index(1) == pair.spec_index(1));
                assert(result.spec_index(0) == x);
                assert(result.spec_index(1) == s.spec_index(index as int));
            } else {
                assert(1 <= i < (s.len() - index));
                assert(result.spec_index(2*i) == rest.spec_index(2*i - 2));
                assert(result.spec_index(2*i + 1) == rest.spec_index(2*i - 1));
                assert(rest.spec_index(2*(i-1)) == x);
                assert(rest.spec_index(2*(i-1) + 1) == s.spec_index((index + 1) + (i-1)));
                assert(2*(i-1) == 2*i - 2);
                assert(2*(i-1) + 1 == 2*i - 1);
                assert((index + 1) + (i-1) == index + i);
            }
        };
        
        result
    }
}

}