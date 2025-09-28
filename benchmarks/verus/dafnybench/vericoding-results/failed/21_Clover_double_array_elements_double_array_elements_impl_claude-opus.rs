use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s[i] == 2 * old(s)[i]
// </vc-spec>
// <vc-code>
{
    let ghost old_s = s@;
    let n = s.len();
    
    for i in 0..n
        invariant
            s.len() == old_s.len(),
            s.len() == n,
            0 <= i <= n,
            forall|j: int| 0 <= j < i ==> #[trigger] s@[j] == 2 * old_s[j],
            forall|j: int| i <= j < n ==> #[trigger] s@[j] == old_s[j],
    {
        let val = s[i];
        let new_val = 2 * val;  // Direct multiplication in i32
        s.set(i, new_val);
        
        assert(s@.len() == old_s.len());
        assert(s@[i as int] == new_val);
        assert(new_val == 2 * val);
        assert(val == old_s[i as int]);
        assert(s@[i as int] == 2 * old_s[i as int]);
    }
    
    assert(forall|i: int| 0 <= i < s.len() ==> #[trigger] s@[i] == 2 * old_s[i]);
}
// </vc-code>

fn main() {
}

}