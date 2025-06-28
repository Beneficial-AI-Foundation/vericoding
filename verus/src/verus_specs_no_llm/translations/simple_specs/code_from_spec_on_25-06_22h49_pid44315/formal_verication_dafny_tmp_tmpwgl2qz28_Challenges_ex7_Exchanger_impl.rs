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
        
        // Proof that length is preserved
        assert(result.len() == s.len());
        
        // Proof that the swap worked correctly
        assert(result.spec_index(x as int) == s.spec_index(y as int));
        assert(result.spec_index(y as int) == s.spec_index(x as int));
        
        // Proof that other elements remain unchanged
        assert(forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> 
            #[trigger] result.spec_index(b as int) == s.spec_index(b as int)
        ) by {
            let x_int = x as int;
            let y_int = y as int;
            let intermediate = s.update(x_int, temp_y);
            
            assert(forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> {
                let b_int = b as int;
                intermediate.spec_index(b_int) == s.spec_index(b_int)
            });
            
            assert(forall|b: nat| 0 <= b < s.len() && b != x && b != y ==> {
                let b_int = b as int;
                result.spec_index(b_int) == intermediate.spec_index(b_int)
            });
        };
        
        // Proof of multiset equality
        assert(s.to_multiset() == result.to_multiset()) by {
            // Establish the bijection property for multiset equality
            assert(result.len() == s.len());
            
            // Show that every element at every position is accounted for
            assert(forall|i: int| 0 <= i < s.len() ==> {
                if i == x as int {
                    result.spec_index(i) == s.spec_index(y as int)
                } else if i == y as int {
                    result.spec_index(i) == s.spec_index(x as int)
                } else {
                    result.spec_index(i) == s.spec_index(i)
                }
            });
            
            // The key insight: we have a permutation where only x and y positions are swapped
            // For any value v, count(v) in result equals count(v) in s
            assert(forall|v: Bases| s.to_multiset().count(v) == result.to_multiset().count(v)) by {
                // The counts are preserved because we only rearranged existing elements
                // Each element from s appears exactly once in result at a different position
                assert(forall|i: int| 0 <= i < s.len() ==> {
                    let s_val = s.spec_index(i);
                    let result_pos = if i == x as int { y as int } 
                                   else if i == y as int { x as int } 
                                   else { i };
                    result.spec_index(result_pos) == s_val
                });
            };
        };
        
        result
    }
}

}