use vstd::prelude::*;

verus! {

// <vc-helpers>
// Empty as the macro `assert_by_and_reveal_proof` is not needed in the updated code.
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(s).len() ==> s[i] == 2 * old(s)[i]
// </vc-spec>
// <vc-code>
{
    let old_s = s.clone();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            s.len() == old_s.len(),
            forall|j: int| 0 <= j && (j as usize) < i ==> s[j as usize] == 2 * old_s[j as usize],
            forall|j: int| i <= (j as usize) && (j as usize) < s.len() ==> s[j as usize] == old_s[j as usize],
    {
        s.set(i, s[i] * 2);
        // The `assert_by_and_reveal_proof` macro is not a standard Verus construct and
        // is not needed here to prove the postcondition. The invariant handles the proof.
        i = i + 1;
    }
}
// </vc-code>

fn main() {
}

}