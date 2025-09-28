use vstd::prelude::*;

verus! {

// <vc-helpers>
// Helper to track original values
ghost fn original_value(s: &Vec<i32>, original_s: &Vec<i32>, index: int) -> (result: i32)
    requires 
        0 <= index < s.len(),
        s.len() == original_s.len(),
    ensures result == original_s[index]
{
    original_s[index]
}
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s[i] == 2 * old(s)[i]
// </vc-spec>
// <vc-code>
{
    let original_s = s.clone();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s.len() == original_s.len(),
            s.len() == old(s).len(),
            original_s == old(s),
            forall|j: int| #![auto] 0 <= j < i ==> s[j] == 2 * original_s[j],
            forall|j: int| #![auto] i <= j < s.len() ==> s[j] == original_s[j],
        decreases s.len() - i,
    {
        let old_val = s[i];
        assert(old_val == original_s[i as int]);
        
        // Check for overflow before multiplication
        assert(old_val.abs() <= i32::MAX / 2);
        
        s.set(i, 2 * old_val);
        
        assert(s[i as int] == 2 * original_s[i as int]);
        
        i += 1;
    }
}
// </vc-code>

fn main() {
}

}