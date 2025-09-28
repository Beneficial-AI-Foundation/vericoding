// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn shares_memory(a: Vec<i8>, b: Vec<i8>) -> bool
{

    true &&

    (a.len() == b.len() && a@ == b@) &&

    true &&

    true
}

fn shares_memory_fn(a: Vec<i8>, b: Vec<i8>) -> (result: bool)
    ensures

        (result == true || result == false) &&

        (a.len() == b.len() && a@ == b@ ==> result == true) &&

        true
// </vc-spec>
// <vc-code>
{
    if a.len() != b.len() {
        return false;
    }

    let mut i: usize = 0;
    while i < a.len()
        invariant
            a.len() == b.len(),
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> a@[j] == b@[j],
        decreases a.len() - i
    {
        if a[i] != b[i] {
            return false;
        }
        i = i + 1;
    }

    true
}
// </vc-code>

}
fn main() {}