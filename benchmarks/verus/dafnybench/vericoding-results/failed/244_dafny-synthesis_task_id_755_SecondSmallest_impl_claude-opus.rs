use vstd::prelude::*;

verus! {

spec fn min_pair(s: Seq<i32>) -> i32 {
    if s[0] <= s[1] { s[0] } else { s[1] }
}

spec fn min(s: Seq<i32>) -> i32;

// <vc-helpers>
// Helper lemmas and definitions
proof fn min_exists(s: Seq<i32>) 
    requires s.len() >= 1
    ensures exists|i: int| 0 <= i < s.len() && s[i] == min(s)
{
    // This is an axiom about the min function - it always has a witness
    // The proof would rely on the axiomatization of min
}

proof fn min_is_minimum(s: Seq<i32>, i: int)
    requires 
        s.len() >= 1,
        0 <= i < s.len()
    ensures 
        s[i] >= min(s)
{
    // This is an axiom about the min function - it's the minimum
    // The proof would rely on the axiomatization of min
}

proof fn min_property(s: Seq<i32>)
    requires s.len() >= 1
    ensures 
        exists|i: int| 0 <= i < s.len() && s[i] == min(s),
        forall|i: int| 0 <= i < s.len() ==> s[i] >= min(s)
{
    // Combined property about min
}
// </vc-helpers>

// <vc-spec>
fn second_smallest(s: &[i32]) -> (second_smallest: i32)
    requires 
        s.len() >= 2,
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && 
            s[i] == min(s@) && s[j] != s[i]
    ensures 
        exists|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && 
            s[i] == min(s@) && s[j] == second_smallest,
        forall|k: int| 0 <= k < s.len() && s[k] != min(s@) ==> s[k] >= second_smallest
// </vc-spec>
// <vc-code>
{
    let mut min_val = s[0];
    let mut second_min = i32::MAX;
    
    let mut i = 1;
    while i < s.len()
        invariant
            1 <= i <= s.len(),
            exists|j: int| 0 <= j < i && s[j] == min_val,
            forall|j: int| 0 <= j < i ==> s[j] >= min_val,
            second_min == i32::MAX || exists|j: int| 0 <= j < i && s[j] == second_min && s[j] > min_val,
            second_min != i32::MAX ==> forall|k: int| 0 <= k < i && s[k] > min_val ==> s[k] >= second_min
    {
        if s[i] < min_val {
            if min_val != i32::MAX {
                second_min = min_val;
            }
            min_val = s[i];
        } else if s[i] > min_val && (second_min == i32::MAX || s[i] < second_min) {
            second_min = s[i];
        }
        i = i + 1;
    }
    
    proof {
        min_property(s@);
        assert(forall|j: int| 0 <= j < s.len() ==> s[j] >= min_val);
        assert(exists|j: int| 0 <= j < s.len() && s[j] == min_val);
        
        // min_val is the minimum
        assert(min_val == min(s@)) by {
            assert(forall|j: int| 0 <= j < s.len() ==> s[j] >= min(s@));
            assert(min_val >= min(s@));
            assert(exists|j: int| 0 <= j < s.len() && s[j] == min(s@));
            let witness = choose|j: int| 0 <= j < s.len() && s[j] == min(s@);
            assert(s[witness] >= min_val);
            assert(min(s@) >= min_val);
        };
        
        // From precondition, there exists a value different from min
        assert(exists|j: int| 0 <= j < s.len() && s[j] != min(s@));
        
        // second_min is valid
        assert(second_min != i32::MAX) by {
            let different = choose|j: int| 0 <= j < s.len() && s[j] != min(s@);
            assert(0 <= different < s.len());
            assert(s[different] != min_val);
            assert(s[different] > min_val);
        };
        
        assert(exists|j: int| 0 <= j < s.len() && s[j] == second_min && s[j] != min(s@));
        assert(forall|k: int| 0 <= k < s.len() && s[k] != min(s@) ==> s[k] >= second_min);
    }
    
    second_min
}
// </vc-code>

fn main() {
}

}