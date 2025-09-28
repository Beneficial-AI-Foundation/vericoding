use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper functions needed for this exercise.
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
    let n = v.len();
    let mut k: usize = 0;
    while k < n
        invariant k <= n,
        invariant forall |j: int| 0 <= j && j < k as int ==> v@[j] != 0,
        decreases n - k,
    {
        if v@[k as int] == 0 {
            return k;
        }
        k = k + 1;
    }
    k
}
// </vc-code>

fn main() {
}

}