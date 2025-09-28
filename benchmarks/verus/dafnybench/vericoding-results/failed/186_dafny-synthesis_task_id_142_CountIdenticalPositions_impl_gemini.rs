// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed, helper is correct. */
spec fn matching_set(a: Seq<int>, b: Seq<int>, c: Seq<int>, k: nat) -> Set<int>
    requires
        a.len() == b.len(),
        b.len() == c.len(),
        k <= a.len(),
{
    Set::new(|i: int| 0 <= i < k && a[i] == b[i] && b[i] == c[i])
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
/* code modified by LLM (iteration 5): fixed compilation errors by correcting paths/names for set_lib APIs. */
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len() && b.len() == c.len(),
            count == matching_set(a, b, c, i as nat).len(),
        decreases a.len() - i
    {
        if a[i] == b[i] && b[i] == c[i] {
            proof {
                let s1 = matching_set(a, b, c, i as nat);
                let s2 = matching_set(a, b, c, (i + 1) as nat);
                let i_int = i as int;
                assert(!s1.contains(i_int));
                vstd::set_lib::assert_sets_equal!(s2, s1.insert(i_int));
                vstd::set_lib::lemma_len_insert(s1, i_int);
            }
            count = count + 1;
        } else {
             proof {
                let s1 = matching_set(a, b, c, i as nat);
                let s2 = matching_set(a, b, c, (i + 1) as nat);
                vstd::set_lib::assert_sets_equal!(s2, s1);
            }
        }
        i = i + 1;
    }
    count
}
// </vc-code>

}
fn main() {}