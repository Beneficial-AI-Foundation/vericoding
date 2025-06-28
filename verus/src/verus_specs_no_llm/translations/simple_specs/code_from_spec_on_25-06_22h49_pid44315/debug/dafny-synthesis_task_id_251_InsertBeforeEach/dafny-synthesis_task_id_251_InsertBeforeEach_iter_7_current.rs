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
            v.spec_index(2*i) == x && v.spec_index(2*i + 1) == s.spec_index((index as int) + i)
    decreases s.len() - index
{
    if index >= s.len() {
        Seq::empty()
    } else {
        let rest = InsertBeforeEachHelper(s, x, index + 1);
        let pair = seq![x, s[index as int]];
        let result = pair + rest;
        
        // Prove length property
        assert(pair.len() == 2);
        assert(rest.len() == 2 * (s.len() - (index + 1)));
        assert(result.len() == pair.len() + rest.len());
        assert(result.len() == 2 + 2 * (s.len() - (index + 1)));
        assert(2 * (s.len() - index) == 2 + 2 * (s.len() - (index + 1))) by {
            assert(s.len() - index == 1 + (s.len() - (index + 1)));
        };
        
        // Prove indexing properties
        assert forall |i: int| 0 <= i < (s.len() - index) implies 
            result.spec_index(2*i) == x && result.spec_index(2*i + 1) == s.spec_index((index as int) + i)
        by {
            assert(0 <= i < (s.len() - index));
            
            if i == 0 {
                // First element pair comes from 'pair'
                assert(2*i == 0);
                assert(2*i + 1 == 1);
                assert(result.spec_index(0) == pair.spec_index(0));
                assert(pair.spec_index(0) == x);
                assert(result.spec_index(1) == pair.spec_index(1));
                assert(pair.spec_index(1) == s[index as int]);
                assert(s[index as int] == s.spec_index(index as int));
                assert((index as int) + i == (index as int) + 0);
                assert((index as int) + 0 == index as int);
            } else {
                // Elements from recursive call
                assert(i >= 1);
                assert(2*i >= 2);
                assert(2*i + 1 >= 3);
                
                // Map to rest indices
                let rest_idx_even = 2*i - 2;
                let rest_idx_odd = 2*i + 1 - 2;
                
                assert(rest_idx_even == 2*(i-1));
                assert(rest_idx_odd == 2*(i-1) + 1);
                
                // Use concatenation properties
                assert(result.spec_index(2*i) == rest.spec_index(rest_idx_even));
                assert(result.spec_index(2*i + 1) == rest.spec_index(rest_idx_odd));
                
                // From recursive call postcondition
                let rest_i = i - 1;
                assert(rest_i >= 0);
                assert(rest_i < s.len() - (index + 1)) by {
                    assert(i < s.len() - index);
                    assert(i - 1 < s.len() - index - 1);
                    assert(s.len() - index - 1 == s.len() - (index + 1));
                };
                
                assert(rest.spec_index(2*rest_i) == x);
                assert(rest.spec_index(2*rest_i + 1) == s.spec_index(((index + 1) as int) + rest_i));
                
                // Connect the indices
                assert(rest_idx_even == 2*rest_i);
                assert(rest_idx_odd == 2*rest_i + 1);
                
                // Arithmetic proof
                assert(((index + 1) as int) + rest_i == (index as int) + i) by {
                    assert((index + 1) as int == (index as int) + 1);
                    assert(rest_i == i - 1);
                    assert(((index + 1) as int) + rest_i == (index as int) + 1 + (i - 1));
                    assert((index as int) + 1 + (i - 1) == (index as int) + i);
                };
                
                // Final conclusions
                assert(result.spec_index(2*i) == x);
                assert(result.spec_index(2*i + 1) == s.spec_index((index as int) + i));
            }
        };
        
        result
    }
}

}