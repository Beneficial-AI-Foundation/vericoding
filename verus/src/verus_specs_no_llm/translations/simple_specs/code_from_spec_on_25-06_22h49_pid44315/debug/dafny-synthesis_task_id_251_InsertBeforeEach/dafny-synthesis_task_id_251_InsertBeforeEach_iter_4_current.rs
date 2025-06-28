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
        let result = pair + rest;
        
        // Help Verus with the length calculation
        assert(pair.len() == 2);
        assert(rest.len() == 2 * (s.len() - (index + 1)));
        assert(result.len() == pair.len() + rest.len());
        
        // Prove length equality step by step
        assert(s.len() - index >= 1) by {
            assert(index < s.len());
        };
        assert(s.len() - (index + 1) == s.len() - index - 1);
        assert(2 * (s.len() - index) == 2 + 2 * (s.len() - (index + 1))) by {
            let remaining = s.len() - index;
            let next_remaining = s.len() - (index + 1);
            assert(remaining == next_remaining + 1);
            assert(2 * remaining == 2 * (next_remaining + 1));
            assert(2 * (next_remaining + 1) == 2 * next_remaining + 2);
        };
        
        // Prove the indexing properties
        assert forall |i: int| 0 <= i < (s.len() - index) implies 
            result.spec_index(2*i) == x && result.spec_index(2*i + 1) == s.spec_index(index + i)
        by {
            let remaining = s.len() - index;
            if i == 0 {
                // Base case: i == 0
                assert(result.spec_index(0) == pair.spec_index(0));
                assert(result.spec_index(1) == pair.spec_index(1));
                assert(pair.spec_index(0) == x);
                assert(pair.spec_index(1) == s.spec_index(index));
                assert(index + 0 == index);
            } else {
                // Recursive case: i > 0
                assert(i >= 1);
                assert(i < remaining);
                let rest_index = i - 1;
                assert(rest_index >= 0);
                assert(rest_index < remaining - 1);
                assert(remaining - 1 == s.len() - (index + 1));
                
                // Use the postcondition of the recursive call
                assert(rest.spec_index(2*rest_index) == x);
                assert(rest.spec_index(2*rest_index + 1) == s.spec_index((index + 1) + rest_index));
                
                // Show that concatenation preserves indexing
                assert(2*i >= 2);
                assert(2*i + 1 >= 3);
                assert(result.spec_index(2*i) == rest.spec_index(2*i - 2)) by {
                    assert(2*i - 2 >= 0);
                    assert(2*i - 2 < rest.len());
                };
                assert(result.spec_index(2*i + 1) == rest.spec_index(2*i + 1 - 2)) by {
                    assert(2*i + 1 - 2 >= 0);
                    assert(2*i + 1 - 2 < rest.len());
                };
                
                // Connect the arithmetic
                assert(2*i - 2 == 2*(i-1));
                assert(2*i + 1 - 2 == 2*(i-1) + 1);
                assert(rest.spec_index(2*(i-1)) == x);
                assert(rest.spec_index(2*(i-1) + 1) == s.spec_index((index + 1) + (i-1)));
                assert((index + 1) + (i - 1) == index + i);
            }
        };
        
        result
    }
}

}