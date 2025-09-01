use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_element(a: &[i32], pos: usize) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        0 <= pos < a.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len() - 1,
        forall|i: int| 0 <= i < pos ==> result[i] == a[i],
        forall|i: int| pos <= i < result.len() ==> result[i] == a[i + 1],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut result: Vec<i32> = Vec::new();

    // first phase: copy elements before pos
    let mut i: usize = 0;
    while i < pos {
        invariant i <= pos;
        invariant result.len() == i;
        invariant forall |k: int|
            !(0 <= k && k < (i as int)) || result[k as usize] == a[k as usize];
        decreases (pos as int) - (i as int);
        result.push(a[i]);
        i = i + 1;
    }

    // after first loop, result.len() == pos and prefix elements equal
    assert(result.len() == pos);

    // second phase: copy elements after pos
    let mut j: usize = pos + 1;
    while j < a.len() {
        invariant j <= a.len();
        invariant result.len() == pos + (j - (pos + 1));
        invariant forall |k: int|
            !(0 <= k && k < (pos as int)) || result[k as usize] == a[k as usize];
        invariant forall |k: int|
            !(pos <= k && k < (result.len() as int)) || result[k as usize] == a[(k as usize) + 1];
        decreases (a.len() as int) - (j as int);
        result.push(a[j]);
        j = j + 1;
    }

    // final checks (can be asserted to help verifier)
    assert(result.len() == a.len() - 1);
    // ensure the prefix and suffix properties hold for all indices
    assert(forall |k: int|
        0 <= k && k < (pos as int) ==> result[k as usize] == a[k as usize]);
    assert(forall |k: int|
        pos <= k && k < (result.len() as int) ==> result[k as usize] == a[(k as usize) + 1]);

    result
    // impl-end
}
// </vc-code>

fn main() {}
}