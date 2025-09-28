// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn all_equal(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s[i] == s[j]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): fixed `assert forall` syntax */
proof fn all_equal_from_first(s: Seq<i32>)
    requires
        s.len() > 0,
        forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] == s[0],
    ensures
        all_equal(s),
{
    assert forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() implies s[i] == s[j] by
    {
        assert(s[i] == s[0]);
        assert(s[j] == s[0]);
    }
}

proof fn all_equal_trivial(s: Seq<i32>)
    requires
        s.len() <= 1,
    ensures
        all_equal(s),
{
}
// </vc-helpers>

// <vc-spec>
fn mall_equal1(v: &[i32]) -> (b: bool)
    ensures b == all_equal(v@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): no change, helper compilation error was the issue */
{
    if v.len() <= 1 {
        proof {
            all_equal_trivial(v@);
        }
        return true;
    }

    let first = v[0];
    let mut i: usize = 1;
    while i < v.len()
        invariant
            v.len() > 1,
            1 <= i <= v.len(),
            first == v@[0],
            forall|k: int| 0 <= k < (i as int) ==> #[trigger] v@[k] == first,
        decreases v.len() - i
    {
        if v[i] != first {
            assert(!all_equal(v@)) by {
                assert(v@[i as int] != v@[0]);
            };
            return false;
        }
        i = i + 1;
    }

    proof {
        all_equal_from_first(v@);
    }
    return true;
}
// </vc-code>

}
fn main() {}