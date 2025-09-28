// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn cube(n: int) -> int {
        n * n * n
}
    
    // </vc-preamble>

// <vc-helpers>
proof fn lemma_cube_bounds(n: u8)
    ensures
        forall|k: int| k > 6 ==> cube(k) > 255,
        forall|k: int| 0 <= k <= n as int && n as int == cube(k) ==> k <= 6,
{
    /* helper modified by LLM (iteration 5): Fixed lemma to prove cube bounds for u8 values */
    assert(cube(7) == 343);
    assert(343 > 255);
    assert forall|k: int| k >= 7 implies cube(k) >= cube(7) by {
        if k >= 7 {
            assert(k * k * k >= 7 * 7 * 7);
        }
    };
    assert forall|k: int| k > 6 implies cube(k) > 255 by {
        if k > 6 {
            assert(k >= 7);
            assert(cube(k) >= cube(7));
            assert(cube(7) == 343);
            assert(343 > 255);
        }
    };
}
// </vc-helpers>

// <vc-spec>
fn is_cube(n: u8) -> (r: bool)
    ensures r == exists|k: int| 0 <= k <= n as int && n as int == cube(k)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed forall assertion syntax */
    let mut k: u8 = 0;
    let mut found = false;
    
    while k <= 6
        invariant
            0 <= k <= 7,
            found == exists|j: int| 0 <= j < k && (n as int) == cube(j),
            !found,
        decreases 7 - k
    {
        let k_cubed = k * k * k;
        if k_cubed == n {
            found = true;
            proof {
                assert((n as int) == cube(k as int));
                assert(0 <= k as int <= (n as int));
            }
            return found;
        }
        k = k + 1;
    }
    
    proof {
        lemma_cube_bounds(n);
        assert forall|j: int| 0 <= j <= (n as int) && (n as int) == cube(j) implies j <= 6 by {
            if 0 <= j <= (n as int) && (n as int) == cube(j) {
                // The lemma ensures this
            }
        };
        assert(!exists|j: int| 0 <= j <= (n as int) && (n as int) == cube(j));
    }
    
    found
}
// </vc-code>


}

fn main() {}