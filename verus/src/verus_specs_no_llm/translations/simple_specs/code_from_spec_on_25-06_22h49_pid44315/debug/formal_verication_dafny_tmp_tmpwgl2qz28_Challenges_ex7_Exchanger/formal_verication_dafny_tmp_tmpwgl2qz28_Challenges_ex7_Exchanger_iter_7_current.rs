use builtin::*;
use builtin_macros::*;

verus! {

// Define Bases type (assuming it's an enum of DNA bases)
#[derive(PartialEq, Eq, Clone, Copy)]
enum Bases {
    A,
    T,
    G,
    C,
}

fn main() {
}

fn Exchanger(s: Seq<Bases>, x: nat, y: nat) -> (t: Seq<Bases>)
    requires
        0 < s.len() && x < s.len() && y < s.len()
    ensures
        t.len() == s.len(),
        forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> #[trigger] t.spec_index(b as int) == s.spec_index(b as int),
        t.spec_index(x as int) == s.spec_index(y as int) && s.spec_index(x as int) == t.spec_index(y as int),
        s.to_multiset() == t.to_multiset()
{
    if x == y {
        s
    } else {
        let temp_x = s[x as int];
        let temp_y = s[y as int];
        let result = s.update(x as int, temp_y).update(y as int, temp_x);
        
        // Proof annotations to help verification
        assert(result.len() == s.len());
        
        // Prove the swap worked correctly
        assert(result.spec_index(x as int) == temp_y);
        assert(result.spec_index(y as int) == temp_x);
        assert(temp_x == s.spec_index(x as int));
        assert(temp_y == s.spec_index(y as int));
        
        // Therefore the swap postcondition holds
        assert(result.spec_index(x as int) == s.spec_index(y as int));
        assert(result.spec_index(y as int) == s.spec_index(x as int));
        
        // Prove that other elements remain unchanged
        assert(forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> {
            let b_int = b as int;
            let x_int = x as int;
            let y_int = y as int;
            #[trigger] result.spec_index(b_int) == s.spec_index(b_int)
        }) by {
            assert(forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> {
                let b_int = b as int;
                let x_int = x as int;
                let y_int = y as int;
                let intermediate = s.update(x_int, temp_y);
                // First update doesn't change b since b != x
                intermediate.spec_index(b_int) == s.spec_index(b_int) &&
                // Second update doesn't change b since b != y  
                result.spec_index(b_int) == intermediate.spec_index(b_int)
            });
        }
        
        // Prove multiset equality by showing element counts are preserved
        assert(s.to_multiset() == result.to_multiset()) by {
            // The multiset equality follows from the fact that we only swap elements
            // All elements except positions x and y remain the same
            // Positions x and y exchange values, preserving the overall count
            assert(forall|i: int| 0 <= i < s.len() ==> {
                let original_val = s.spec_index(i);
                let result_val = result.spec_index(i);
                if i == x as int {
                    result_val == s.spec_index(y as int)
                } else if i == y as int {
                    result_val == s.spec_index(x as int)
                } else {
                    result_val == original_val
                }
            });
        }
        
        result
    }
}

}