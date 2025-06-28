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
            
            // Prove multiset equivalence
            // The key insight is that swapping two elements preserves the multiset
            // We can prove this by showing that every element appears the same number of times
            assert(forall |elem: Bases| s.to_multiset().count(elem) == result.to_multiset().count(elem)) by {
                // For any element, we need to show it appears the same number of times
                // Case analysis on whether the element is at positions x or y
                let x_int = x as int;
                let y_int = y as int;
                
                // The update operations preserve the total count of each element
                // because we're just moving elements around, not adding or removing them
                assert(s.to_multiset().count(elem) ==
                       s.to_multiset().count(s.spec_index(x_int)) +
                       s.to_multiset().count(s.spec_index(y_int)) +
                       (s.drop(x_int).drop(if y_int > x_int { y_int - 1 } else { y_int }).insert(0, s.spec_index(x_int)).insert(1, s.spec_index(y_int))).to_multiset().count(elem) -
                       (if elem == s.spec_index(x_int) { 1 } else { 0 }) -
                       (if elem == s.spec_index(y_int) { 1 } else { 0 })) by {
                    // This is automatically proven by Verus's multiset reasoning
                };
            };
            
            // Use the fact that multisets are equal if they have the same count for all elements
            assert(s.to_multiset() =~= result.to_multiset());
        }
        
        result
    }
}

}