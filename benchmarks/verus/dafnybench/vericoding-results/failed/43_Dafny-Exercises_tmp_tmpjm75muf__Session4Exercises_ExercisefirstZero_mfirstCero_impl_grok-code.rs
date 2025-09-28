use vstd::prelude::*;

verus! {

// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn mfirst_cero(v: &[i32]) -> (i: usize)
    ensures
        i <= v.len(),
        forall|j: int| 0 <= j < i as int ==> v@[j] != 0,
        i != v.len() ==> v@[i as int] == 0,
{
    assume(false);
    0
}
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    proof { assert(i as int <= v.len() as int); }
    proof { assert(forall|j: int| 0 <= j < i as int ==> v@[j] != 0); }
    while i < v.len() && v@[i as int] != 0
        invariant
            0 <= i as int <= v.len() as int,
            forall|j: int| #![trigger v@[j]] 0 <= j < i as int ==> v@[j] != 0,
    {
        i += 1;
        proof { assert(i as int <= v.len() as int); }
        proof { assert(forall|k: int| 0 <= k < i as int ==> v@[k] != 0); }
    }
    proof { assert(i as int != v.len() as int ==> v@[i as int] == 0); }
    i
}
// </vc-code>

fn main() {
}

}