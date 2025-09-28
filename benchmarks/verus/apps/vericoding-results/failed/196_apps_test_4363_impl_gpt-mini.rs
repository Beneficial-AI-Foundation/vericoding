// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(k: int, s: int) -> bool {
    k >= 0 && s >= 0 && s <= 3 * k
}

spec fn is_valid_triple(k: int, s: int, x: int, y: int, z: int) -> bool {
    0 <= x <= k && 0 <= y <= k && 0 <= z <= k && x + y + z == s
}

spec fn count_valid_triples(k: int, s: int) -> int
    recommends k >= 0
{
    count_valid_triples_helper(k, s, 0)
}

spec fn count_valid_triples_helper(k: int, s: int, z: int) -> int
    recommends k >= 0, z >= 0
    decreases if k >= z { k + 1 - z } else { 0 }
{
    if z > k { 0 }
    else { count_valid_triples_for_z(k, s, z) + count_valid_triples_helper(k, s, z + 1) }
}

spec fn count_valid_triples_for_z(k: int, s: int, z: int) -> int
    recommends k >= 0, z >= 0
{
    count_valid_triples_for_z_helper(k, s, z, 0)
}

spec fn count_valid_triples_for_z_helper(k: int, s: int, z: int, y: int) -> int
    recommends k >= 0, z >= 0, y >= 0
    decreases if k >= y { k + 1 - y } else { 0 }
{
    if y > k { 0 }
    else { 
        let x = s - y - z;
        let this_count: int = if 0 <= x <= k { 1 } else { 0 };
        this_count + count_valid_triples_for_z_helper(k, s, z, y + 1)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): nonnegativity for count_valid_triples_for_z_helper */
proof fn lemma_count_for_z_helper_nonneg(k: int, s: int, z: int, y: int)
    requires k >= 0, z >= 0, y >= 0,
    ensures count_valid_triples_for_z_helper(k, s, z, y) >= 0,
    decreases if k >= y { k + 1 - y } else { 0 }
{
    if y > k {
        // base case: count_valid_triples_for_z_helper returns 0
    } else {
        lemma_count_for_z_helper_nonneg(k, s, z, y + 1);
        proof {
            // unfold one step and use induction hypothesis
            assert((if 0 <= s - y - z <= k { 1 as int } else { 0 as int }) >= 0);
            assert(count_valid_triples_for_z_helper(k, s, z, y + 1) >= 0);
            assert(count_valid_triples_for_z_helper(k, s, z, y) ==
                (if 0 <= s - y - z <= k { 1 as int } else { 0 as int })
                + count_valid_triples_for_z_helper(k, s, z, y + 1));
            assert(count_valid_triples_for_z_helper(k, s, z, y) >= 0);
        }
    }
}

/* helper modified by LLM (iteration 5): nonnegativity for count_valid_triples_for_z */
proof fn lemma_count_for_z_nonneg(k: int, s: int, z: int)
    requires k >= 0, z >= 0,
    ensures count_valid_triples_for_z(k, s, z) >= 0,
{
    lemma_count_for_z_helper_nonneg(k, s, z, 0 as int);
}

/* helper modified by LLM (iteration 5): nonnegativity helper over z */
proof fn lemma_count_nonneg_helper(k: int, s: int, z: int)
    requires k >= 0, z >= 0,
    ensures count_valid_triples_helper(k, s, z) >= 0,
    decreases if k >= z { k + 1 - z } else { 0 }
{
    if z > k {
        // base case: returns 0
    } else {
        lemma_count_for_z_nonneg(k, s, z);
        lemma_count_nonneg_helper(k, s, z + 1);
        proof {
            assert(count_valid_triples_helper(k, s, z) ==
                count_valid_triples_for_z(k, s, z) + count_valid_triples_helper(k, s, z + 1));
            assert(count_valid_triples_for_z(k, s, z) >= 0);
            assert(count_valid_triples_helper(k, s, z + 1) >= 0);
            assert(count_valid_triples_helper(k, s, z) >= 0);
        }
    }
}

/* helper modified by LLM (iteration 5): top-level nonnegativity */
proof fn lemma_count_nonneg(k: int, s: int)
    requires k >= 0,
    ensures count_valid_triples(k, s) >= 0,
{
    lemma_count_nonneg_helper(k, s, 0 as int);
}

// </vc-helpers>

// <vc-spec>
fn count_triples(k: i8, s: i8) -> (count: i8)
    requires
        valid_input(k as int, s as int),
    ensures
        count as int == count_valid_triples(k as int, s as int),
        count >= 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative implementation using i8 counters and ghost proofs */
    let mut z: i8 = 0;
    let mut acc: i8 = 0;
    while z <= k
        invariant
            0 <= z as int && z as int <= k as int + 1,
            acc as int == count_valid_triples_helper(k as int, s as int, 0 as int) - count_valid_triples_helper(k as int, s as int, z as int),
        decreases (k as int) - (z as int)
    {
        let mut y: i8 = 0;
        while y <= k
            invariant
                0 <= y as int && y as int <= k as int + 1,
                acc as int ==
                    count_valid_triples_helper(k as int, s as int, 0 as int)
                    - count_valid_triples_helper(k as int, s as int, z as int)
                    + count_valid_triples_for_z_helper(k as int, s as int, z as int, 0 as int)
                    - count_valid_triples_for_z_helper(k as int, s as int, z as int, y as int),
            decreases (k as int) - (y as int)
        {
            let x: i8 = s - y - z;
            let valid: bool = x >= 0 && x <= k;
            proof {
                // relate the runtime check to the spec unfolding
                assert(count_valid_triples_for_z_helper(k as int, s as int, z as int, y as int)
                    == (if x as int >= 0 && x as int <= k as int { 1 as int } else { 0 as int })
                    + count_valid_triples_for_z_helper(k as int, s as int, z as int, y as int + 1));
            }
            if valid {
                acc = acc + 1;
            }
            y = y + 1;
            proof {
                assert(acc as int ==
                    count_valid_triples_helper(k as int, s as int, 0 as int)
                    - count_valid_triples_helper(k as int, s as int, z as int)
                    + count_valid_triples_for_z_helper(k as int, s as int, z as int, 0 as int)
                    - count_valid_triples_for_z_helper(k as int, s as int, z as int, y as int));
            }
        }
        z = z + 1;
        proof {
            // maintain relation between acc and helper after advancing z
            assert(count_valid_triples_helper(k as int, s as int, z as int - 1) ==
                count_valid_triples_for_z(k as int, s as int, z as int - 1) + count_valid_triples_helper(k as int, s as int, z as int));
            assert(acc as int == count_valid_triples_helper(k as int, s as int, 0 as int) - count_valid_triples_helper(k as int, s as int, z as int));
        }
    }
    acc
}

// </vc-code>


}

fn main() {}