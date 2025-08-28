use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_first_zero(v: Seq<i32>, i: int)
    requires
        0 <= i <= v.len(),
        forall|j: int| 0 <= j < i ==> v[j] != 0,
        i < v.len() ==> v[i] == 0,
    ensures
        forall|k: int| 0 <= k < i ==> v[k] != 0,
        i < v.len() ==> v[i] == 0,
{
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
fn first_cero(v: &[i32]) -> (i: usize)
    ensures
        i <= v.len(),
        forall|j: int| 0 <= j < i as int ==> v@[j] != 0,
        i != v.len() ==> v@[i as int] == 0,
{
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            forall|j: int| 0 <= j < i as int ==> v@[j] != 0,
        decreases
            v.len() - i,
    {
        if v[i] == 0 {
            return i;
        }
        i = i + 1;
    }
    i
}
// </vc-code>

fn main() {
}

}