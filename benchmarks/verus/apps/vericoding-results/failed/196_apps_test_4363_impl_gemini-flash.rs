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
/* code modified by LLM (iteration 5): [Fixed comparison of int to i8 (primitive type)] */
{
    let mut count: i8 = 0;

    let ghost k_val = k as int;
    let ghost s_val = s as int;

    // Iterate over z from 0 to k
    let mut z_i: i8 = 0;
    while z_i <= k
        invariant
            0 <= z_i,
            z_i <= k + 1,
            z_i as int <= k_val + 1,
            count as int == count_valid_triples_helper(k_val, s_val, 0) - count_valid_triples_helper(k_val, s_val, z_i as int),
            count >= 0,
        decreases (k as int) + 1 - (z_i as int)
    {
        // Iterate over y from 0 to k
        let mut y_i: i8 = 0;
        while y_i <= k
            invariant
                0 <= z_i,
                z_i <= k, // z_i is at most k within this inner loop, though it can become k+1 after the inner loop finishes
                0 <= y_i,
                y_i <= k + 1,
                y_i as int <= k_val + 1,
                count as int == (count_valid_triples_helper(k_val, s_val, 0) - count_valid_triples_helper(k_val, s_val, z_i as int)) + (count_valid_triples_for_z_helper(k_val, s_val, z_i as int, 0) - count_valid_triples_for_z_helper(k_val, s_val, z_i as int, y_i as int)),
                count >= 0,
            decreases (k as int) + 1 - (y_i as int)
        {
            let ghost y_val = y_i as int;
            let ghost z_val = z_i as int;
            let ghost x_val: int = s_val - y_val - z_val;

            if (0 as int) <= x_val && x_val <= k_val {
                count = count + 1;
            }
            y_i = y_i + 1;
        }
        z_i = z_i + 1;
    }
    count
}
// </vc-code>


}

fn main() {}