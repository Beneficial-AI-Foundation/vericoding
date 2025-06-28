use builtin::*;
use builtin_macros::*;

verus! {

// Define the Bases type (assuming it's some kind of base/nucleotide type)
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum Bases {
    A,
    T,
    G,
    C,
}

fn main() {
}

fn Exchanger(s: Seq<Bases>, x: usize, y: usize) -> (t: Seq<Bases>)
    requires
        0 < s.len() && x < s.len() && y < s.len()
    ensures
        t.len() == s.len(),
        forall |b: usize| b < s.len() && b != x && b != y ==> t.spec_index(b as int) == s.spec_index(b as int),
        t.spec_index(x as int) == s.spec_index(y as int) && s.spec_index(x as int) == t.spec_index(y as int),
        s.to_multiset() == t.to_multiset()
{
    if x == y {
        s
    } else {
        // Get the values at positions x and y
        let temp_x = s[x as int];
        let temp_y = s[y as int];
        
        // Create the swapped sequence
        let result = s.update(x as int, temp_y).update(y as int, temp_x);
        
        proof {
            // Prove length preservation
            assert(result.len() == s.len());
            
            // Prove that non-swapped elements remain unchanged
            assert(forall |b: usize| b < s.len() && b != x && b != y ==> {
                let b_int = b as int;
                let x_int = x as int;
                let y_int = y as int;
                
                // For positions that are neither x nor y, the value remains unchanged
                let after_first_update = s.update(x_int, temp_y);
                // Since b_int != x_int, the first update doesn't change position b_int
                after_first_update.spec_index(b_int) == s.spec_index(b_int) &&
                // Since b_int != y_int, the second update doesn't change position b_int
                result.spec_index(b_int) == after_first_update.spec_index(b_int) &&
                result.spec_index(b_int) == s.spec_index(b_int)
            });
            
            // Prove the swap occurred correctly
            let after_first_update = s.update(x as int, temp_y);
            assert(after_first_update.spec_index(x as int) == temp_y);
            assert(after_first_update.spec_index(y as int) == s.spec_index(y as int)); // y unchanged after first update
            
            assert(result.spec_index(x as int) == temp_y); // Still temp_y after second update
            assert(result.spec_index(y as int) == temp_x); // Now temp_x after second update
            
            // Final swap verification
            assert(result.spec_index(x as int) == s.spec_index(y as int));
            assert(result.spec_index(y as int) == s.spec_index(x as int));
            
            // Prove multiset equivalence using axiom_seq_update_to_multiset
            axiom_seq_update_to_multiset(s, x as int, temp_y);
            let intermediate = s.update(x as int, temp_y);
            axiom_seq_update_to_multiset(intermediate, y as int, temp_x);
            
            // Key insight: when we update position y with temp_x (which was originally at position x),
            // and we already updated position x with temp_y (which was originally at position y),
            // we've essentially just swapped the elements, preserving the multiset
            assert(s.to_multiset() == result.to_multiset());
        }
        
        result
    }
}

}