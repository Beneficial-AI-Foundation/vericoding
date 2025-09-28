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
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < i as int ==> #[trigger] v@[j] != 0,
    {
        if v@[i as int] == 0 {
            break;
        }
        i = i + 1;
    }
    i
}
// </vc-code>

fn main() {
}

}