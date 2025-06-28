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
        assert(2 * (s.len() - index) == 2 + 2 * (s.len() - (index + 1))) by {
            assert(s.len() - index == 1 + (s.len() - (index + 1)));
            assert(2 * (s.len() - index) == 2 * (1 + (s.len() - (index + 1))));
            assert(2 * (1 + (s.len() - (index + 1))) == 2 + 2 * (s.len() - (index + 1)));
        };
        
        // Prove the indexing properties
        assert forall |i: int| 0 <= i < (s.len() - index) implies 
            result.spec_index(2*i) == x && result.spec_index(2*i + 1) == s.spec_index(index + i)
        by {
            if i == 0 {
                // Base case: i == 0
                assert(2*i == 0);
                assert(2*i + 1 == 1);
                assert(result.spec_index(0) == pair.spec_index(0));
                assert(result.spec_index(1) == pair.spec_index(1));
                assert(pair.spec_index(0) == x);
                assert(pair.spec_index(1) == s.spec_index(index as int));
                assert(index + i == index + 0);
                assert(index + 0 == index);
            } else {
                // Recursive case: i > 0
                assert(i >= 1);
                assert(i < s.len() - index);
                assert(i - 1 >= 0);
                assert(i - 1 < s.len() - (index + 1)) by {
                    assert(i < s.len() - index);
                    assert(i - 1 < s.len() - index - 1);
                    assert(s.len() - index - 1 == s.len() - (index + 1));
                };
                
                // Use the postcondition of the recursive call
                assert(rest.spec_index(2*(i-1)) == x);
                assert(rest.spec_index(2*(i-1) + 1) == s.spec_index((index + 1) + (i-1)));
                
                // Show arithmetic relationships
                assert(2*i == 2*(i-1) + 2) by {
                    assert(2*i == 2*i - 2 + 2);
                    assert(2*i - 2 == 2*(i-1));
                };
                assert(2*i + 1 == 2*(i-1) + 3) by {
                    assert(2*i + 1 == 2*i - 2 + 3);
                    assert(2*i - 2 == 2*(i-1));
                };
                assert(2*(i-1) + 1 + 2 == 2*(i-1) + 3);
                
                // Show index relationships in concatenated sequence
                assert(result.spec_index(2*i) == result.spec_index(2*(i-1) + 2));
                assert(result.spec_index(2*(i-1) + 2) == rest.spec_index(2*(i-1)));
                assert(result.spec_index(2*i + 1) == result.spec_index(2*(i-1) + 3));
                assert(result.spec_index(2*(i-1) + 3) == rest.spec_index(2*(i-1) + 1));
                
                // Show the final equality
                assert((index + 1) + (i - 1) == index + i) by {
                    assert(index + 1 + i - 1 == index + i);
                };
            }
        };
        
        result
    }
}

}