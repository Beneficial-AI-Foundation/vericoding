use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    for i in 0..v.len()
        invariant
            forall|j: int| 0 <= j < i as int ==> v@[j] != 0,
    {
        if v[i] == 0 {
            return i;
        }
    }
    v.len()
}
// </vc-code>

fn main() {
}

}