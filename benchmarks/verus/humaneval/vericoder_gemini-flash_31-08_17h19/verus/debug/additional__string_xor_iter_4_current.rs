use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn string_xor(a: &[char], b: &[char]) -> (result: Vec<char>)
    // pre-conditions-start
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i && i < a.len() ==> a[i] == '0' || a[i] == '1',
        forall|i: int| 0 <= i && i < b.len() ==> b[i] == '0' || b[i] == '1',
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i && i < result.len() ==> (result[i] == '0' || result[i] == '1'),
        forall|i: int| 0 <= i && i < result.len() ==> result[i] == (if a[i] == b[i] { '0' } else { '1' })
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut result: Vec<char> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            result.capacity() == a.len(),
            forall|j: int| 0 <= j && (j as usize) < i ==> (result.tracked_vec().borrow().seq_builtin_index(j as nat) == '0' || result.tracked_vec().borrow().seq_builtin_index(j as nat) == '1'),
            forall|j: int| 0 <= j && (j as usize) < i ==> result.tracked_vec().borrow().seq_builtin_index(j as nat) == (if a[j as usize] == b[j as usize] { '0' } else { '1' }),
            // The following invariant is crucial for Verus to understand that a[j as usize] and b[j as usize] are valid accesses.
            // It relies on the pre-conditions that a and b have characters '0' or '1'.
            forall|j: int| 0 <= j && (j as usize) < i ==> ( #[trigger] a[j as usize] == '0' || #[trigger] a[j as usize] == '1' ),
            forall|j: int| 0 <= j && (j as usize) < i ==> ( #[trigger] b[j as usize] == '0' || #[trigger] b[j as usize] == '1' ),
    {
        let res_char: char;
        if a[i] == b[i] {
            res_char = '0';
        } else {
            res_char = '1';
        }
        result.push(res_char);
        i = i + 1;
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}