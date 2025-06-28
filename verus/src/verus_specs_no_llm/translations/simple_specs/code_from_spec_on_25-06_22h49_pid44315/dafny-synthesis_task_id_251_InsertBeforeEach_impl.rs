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

fn InsertBeforeEachHelper(s: Seq<int>, x: int, index: int) -> (v: Seq<int>)
    requires
        0 <= index <= s.len()
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
        let pair = seq![x, s.spec_index(index)];
        let result = pair + rest;
        
        // Prove length property
        assert(pair.len() == 2);
        assert(rest.len() == 2 * (s.len() - (index + 1)));
        assert(result.len() == pair.len() + rest.len());
        assert(result.len() == 2 + 2 * (s.len() - (index + 1)));
        assert(result.len() == 2 * (s.len() - index));
        
        // Prove indexing properties
        assert forall |i: int| 0 <= i < (s.len() - index) implies 
            result.spec_index(2*i) == x && result.spec_index(2*i + 1) == s.spec_index(index + i)
        by {
            if i == 0 {
                // First element pair comes from 'pair'
                assert(result.spec_index(0) == pair.spec_index(0));
                assert(pair.spec_index(0) == x);
                assert(result.spec_index(1) == pair.spec_index(1));
                assert(pair.spec_index(1) == s.spec_index(index));
                assert(s.spec_index(index) == s.spec_index(index + 0));
            } else {
                // Elements from recursive call
                assert(i >= 1);
                assert(0 <= i < s.len() - index);
                
                // Map to rest indices
                let rest_i = i - 1;
                assert(rest_i == i - 1);
                assert(0 <= rest_i);
                assert(rest_i < s.len() - index - 1);
                assert(rest_i < s.len() - (index + 1));
                
                // Use concatenation properties
                assert(2*i >= 2);
                assert(2*i + 1 >= 3);
                assert(result.spec_index(2*i) == rest.spec_index(2*i - 2));
                assert(result.spec_index(2*i + 1) == rest.spec_index(2*i + 1 - 2));
                
                // From recursive call postcondition
                assert(rest.spec_index(2*rest_i) == x);
                assert(rest.spec_index(2*rest_i + 1) == s.spec_index((index + 1) + rest_i));
                
                // Connect the indices
                assert(2*i - 2 == 2*rest_i);
                assert(2*i + 1 - 2 == 2*rest_i + 1);
                
                // Therefore
                assert(result.spec_index(2*i) == x);
                
                // Arithmetic proof for the second index
                assert((index + 1) + rest_i == index + 1 + (i - 1));
                assert(index + 1 + (i - 1) == index + i);
                assert(result.spec_index(2*i + 1) == s.spec_index(index + i));
            }
        };
        
        result
    }
}

}