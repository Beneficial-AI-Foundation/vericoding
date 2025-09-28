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
{
    /* code modified by LLM (iteration 5): Use int arithmetic to avoid overflow and fix invariants */
    let k_int = k as int;
    let s_int = s as int;
    let mut count: int = 0;
    let mut z: int = 0;
    while z <= k_int
        invariant
            0 <= z <= k_int + 1,
            count + count_valid_triples_helper(k_int, s_int, z) == count_valid_triples(k_int, s_int),
        decreases k_int + 1 - z
    {
        let mut y: int = 0;
        while y <= k_int
            invariant
                0 <= y <= k_int + 1,
                count + count_valid_triples_for_z_helper(k_int, s_int, z, y) + count_valid_triples_helper(k_int, s_int, z + 1) == count_valid_triples(k_int, s_int),
            decreases k_int + 1 - y
        {
            let x = s_int - y - z;
            if 0 <= x && x <= k_int {
                count += 1;
            }
            y += 1;
        }
        z += 1;
    }
    assert(count <= i8::MAX as int);
    count as i8
}
// </vc-code>


}

fn main() {}