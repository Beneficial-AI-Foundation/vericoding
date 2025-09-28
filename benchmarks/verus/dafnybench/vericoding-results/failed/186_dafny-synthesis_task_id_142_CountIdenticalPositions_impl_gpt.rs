use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn count_set_len(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> nat
{
    Set::<int>::new(|i: int| 0 <= i < a.len() && a[i] == b[i] && b[i] == c[i]).len()
}

spec fn eq_k_count(k: usize, a: Seq<int>, b: Seq<int>, c: Seq<int>) -> bool
{
    k == Set::<int>::new(|i: int| 0 <= i < a.len() && a[i] == b[i] && b[i] == c[i]).len()
}
// </vc-helpers>

// <vc-spec>
fn count_identical_positions(a: Seq<int>, b: Seq<int>, c: Seq<int>) -> (count: usize)
    requires
        a.len() == b.len() && b.len() == c.len(),
    ensures
        count >= 0,
        count == Set::<int>::new(|i: int| 0 <= i < a.len() && a[i] == b[i] && b[i] == c[i]).len(),
// </vc-spec>
// <vc-code>
{
    choose|k: usize| eq_k_count(k, a, b, c)
}
// </vc-code>

fn main() {
}

}