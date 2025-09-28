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
/* helper modified by LLM (iteration 5): fixed arithmetic reasoning and bounds */
proof fn lemma_count_valid_triples_for_z_helper_bounds(k: int, s: int, z: int, y: int)
    requires k >= 0, z >= 0, y >= 0
    ensures count_valid_triples_for_z_helper(k, s, z, y) <= k + 1 - y
    decreases if k >= y { k + 1 - y } else { 0 }
{
    if y > k {
        assert(count_valid_triples_for_z_helper(k, s, z, y) == 0);
        assert(k + 1 - y <= 0);
    } else {
        lemma_count_valid_triples_for_z_helper_bounds(k, s, z, y + 1);
        assert(count_valid_triples_for_z_helper(k, s, z, y + 1) <= k + 1 - (y + 1));
        assert(count_valid_triples_for_z_helper(k, s, z, y) <= 1 + count_valid_triples_for_z_helper(k, s, z, y + 1));
        assert(1 + (k + 1 - (y + 1)) == k + 1 - y);
    }
}

proof fn lemma_count_valid_triples_for_z_bounds(k: int, s: int, z: int)
    requires k >= 0, z >= 0
    ensures count_valid_triples_for_z(k, s, z) <= k + 1
{
    lemma_count_valid_triples_for_z_helper_bounds(k, s, z, 0);
    assert(count_valid_triples_for_z(k, s, z) == count_valid_triples_for_z_helper(k, s, z, 0));
    assert(count_valid_triples_for_z_helper(k, s, z, 0) <= k + 1 - 0);
}

proof fn lemma_count_valid_triples_helper_bounds(k: int, s: int, z: int)
    requires k >= 0, z >= 0
    ensures count_valid_triples_helper(k, s, z) <= (k + 1 - z) * (k + 1)
    decreases if k >= z { k + 1 - z } else { 0 }
{
    if z > k {
        assert(count_valid_triples_helper(k, s, z) == 0);
        assert(k + 1 - z <= 0);
    } else {
        lemma_count_valid_triples_for_z_bounds(k, s, z);
        lemma_count_valid_triples_helper_bounds(k, s, z + 1);
        assert(count_valid_triples_for_z(k, s, z) <= k + 1);
        assert(count_valid_triples_helper(k, s, z + 1) <= (k + 1 - (z + 1)) * (k + 1));
        assert(count_valid_triples_helper(k, s, z) == count_valid_triples_for_z(k, s, z) + count_valid_triples_helper(k, s, z + 1));
        assert((k + 1) + (k - z) * (k + 1) == (1 + (k - z)) * (k + 1));
        assert((1 + (k - z)) * (k + 1) == (k + 1 - z) * (k + 1));
    }
}

proof fn lemma_count_valid_triples_bounds(k: int, s: int)
    requires k >= 0
    ensures count_valid_triples(k, s) <= (k + 1) * (k + 1)
{
    lemma_count_valid_triples_helper_bounds(k, s, 0);
    assert(count_valid_triples(k, s) == count_valid_triples_helper(k, s, 0));
    assert(count_valid_triples_helper(k, s, 0) <= (k + 1 - 0) * (k + 1));
}

proof fn lemma_arithmetic_bounds(k: int, s: int, y: int, z: int)
    requires 0 <= k, 0 <= s, 0 <= y <= k, 0 <= z <= k, s <= 3 * k
    ensures s - y - z >= -(k + k), s - y - z <= s
{
    assert(y <= k && z <= k);
    assert(s - y - z >= s - k - k);
    assert(s - y - z <= s);
}

proof fn lemma_loop_invariant_preservation(k: int, s: int, z: int, y: int, old_z_count: int, new_z_count: int)
    requires
        0 <= k, 0 <= s, 0 <= y <= k, 0 <= z <= k, s <= 3 * k,
        old_z_count == count_valid_triples_for_z(k, s, z) - count_valid_triples_for_z_helper(k, s, z, y),
        new_z_count == count_valid_triples_for_z(k, s, z) - count_valid_triples_for_z_helper(k, s, z, y + 1),
    ensures new_z_count == old_z_count + (if 0 <= s - y - z <= k { 1 } else { 0 })
{
    let x = s - y - z;
    let this_count = if 0 <= x <= k { 1 } else { 0 };
    assert(count_valid_triples_for_z_helper(k, s, z, y) == this_count + count_valid_triples_for_z_helper(k, s, z, y + 1));
}

proof fn lemma_outer_loop_invariant_preservation(k: int, s: int, z: int, old_count: int, new_count: int, z_count: int)
    requires
        0 <= k, 0 <= s, 0 <= z <= k, s <= 3 * k,
        old_count == count_valid_triples(k, s) - count_valid_triples_helper(k, s, z),
        z_count == count_valid_triples_for_z(k, s, z),
        new_count == old_count + z_count,
    ensures new_count == count_valid_triples(k, s) - count_valid_triples_helper(k, s, z + 1)
{
    if z > k {
        assert(count_valid_triples_helper(k, s, z) == 0);
        assert(count_valid_triples_helper(k, s, z + 1) == 0);
    } else {
        assert(count_valid_triples_helper(k, s, z) == count_valid_triples_for_z(k, s, z) + count_valid_triples_helper(k, s, z + 1));
    }
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
    /* code modified by LLM (iteration 5): use ghost variables for int conversions */
    let mut count = 0i8;
    let mut z = 0i8;
    
    proof {
        lemma_count_valid_triples_bounds(k as int, s as int);
    }
    
    while z <= k
        invariant
            0 <= z <= k + 1,
            count as int == count_valid_triples(k as int, s as int) - count_valid_triples_helper(k as int, s as int, z as int),
            count >= 0,
            count <= 127,
        decreases k - z
    {
        let mut y = 0i8;
        let mut z_count = 0i8;
        
        while y <= k
            invariant
                0 <= y <= k + 1,
                0 <= z <= k,
                z_count as int == count_valid_triples_for_z(k as int, s as int, z as int) - count_valid_triples_for_z_helper(k as int, s as int, z as int, y as int),
                z_count >= 0,
                z_count <= 127,
            decreases k - y
        {
            proof {
                lemma_arithmetic_bounds(k as int, s as int, y as int, z as int);
                lemma_loop_invariant_preservation(k as int, s as int, z as int, y as int, z_count as int, z_count as int + (if 0 <= s as int - y as int - z as int <= k as int { 1 } else { 0 }));
                
                let y_int = y as int;
                let z_int = z as int;
                let s_int = s as int;
                let k_int = k as int;
                
                if y_int + z_int <= s_int {
                    let x_int = s_int - y_int - z_int;
                    if x_int >= 0 && x_int <= k_int {
                        assert(z_count < 127);
                    }
                }
            }
            
            if (y as i16) + (z as i16) <= (s as i16) {
                let x = s - y - z;
                if x >= 0 && x <= k {
                    z_count = z_count + 1;
                }
            }
            y = y + 1;
        }
        
        proof {
            lemma_outer_loop_invariant_preservation(k as int, s as int, z as int, count as int, count as int + z_count as int, z_count as int);
        }
        
        assert(count + z_count <= 127);
        count = count + z_count;
        z = z + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}