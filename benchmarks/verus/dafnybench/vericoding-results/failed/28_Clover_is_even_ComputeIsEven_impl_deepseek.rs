use vstd::prelude::*;

verus! {

// <vc-helpers>
proof lemma_mod_2_equiv(x: int)
    ensures
        (x % 2 == 0) == even(x),
        (x % 2 != 0) == !even(x),
{
    assert(even(x) <==> exists|k: int| x == 2 * k);
    if x % 2 == 0 {
        assert(x % 2 == 0 ==> even(x)) by {
            let k = x / 2;
            assert(x == 2 * k);
            assert(even(x));
        };
    } else {
        assert(x % 2 != 0 ==> !even(x)) by {
            assert(forall|y: int| y % 2 == 0 || y % 2 == 1 || y % 2 == -1);
            if x % 2 == 1 {
                assert(forall|k: int| x != 2 * k);
            } else {
                assert(x % 2 == -1);
                assert(forall|k: int| x != 2 * k);
            }
            assert(!even(x));
        };
    }
}

spec fn even(x: int) -> bool {
    exists|k: int| x == 2 * k
}
// </vc-helpers>

// <vc-spec>
fn compute_is_even(x: int) -> (is_even: bool)
    ensures (x % 2 == 0) == is_even
// </vc-spec>
// <vc-code>
{
    proof { lemma_mod_2_equiv(x); }
    x % 2 == 0
}
// </vc-code>

fn main() {
}

}