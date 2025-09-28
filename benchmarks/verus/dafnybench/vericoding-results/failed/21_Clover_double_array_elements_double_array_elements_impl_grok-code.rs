use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this verification
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s[i] == 2 * old(s)[i]
// </vc-spec>
// <vc-code>
{
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall|j: int| #![auto] (0 <= j < i) ==> s[j] == 2 * old(s)[j]
        decreases
            s.len() - i
    {
        let val = s[i];
        proof { assert ((2 * (val as int)) >= i32::MIN as int && (2 * (val as int)) <= i32::MAX as int); }
        s.set(i, 2 * val);
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}