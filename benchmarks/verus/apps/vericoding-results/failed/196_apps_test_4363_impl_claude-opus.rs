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
/* helper modified by LLM (iteration 5): Added recursive proof for count bounds and non-negativity */
proof fn lemma_count_bounded(k: int, s: int)
    requires
        valid_input(k, s),
    ensures
        count_valid_triples(k, s) <= (k + 1) * (k + 1),
        count_valid_triples(k, s) >= 0,
{
    lemma_count_helper_bounded(k, s, 0);
}

proof fn lemma_count_helper_bounded(k: int, s: int, z: int)
    requires
        k >= 0,
        z >= 0,
    ensures
        count_valid_triples_helper(k, s, z) <= (k + 1 - z) * (k + 1),
        count_valid_triples_helper(k, s, z) >= 0,
    decreases k + 1 - z,
{
    if z > k {
        assert(count_valid_triples_helper(k, s, z) == 0);
    } else {
        lemma_count_for_z_bounded(k, s, z);
        lemma_count_helper_bounded(k, s, z + 1);
        assert(count_valid_triples_helper(k, s, z) == count_valid_triples_for_z(k, s, z) + count_valid_triples_helper(k, s, z + 1));
    }
}

proof fn lemma_count_for_z_bounded(k: int, s: int, z: int)
    requires
        k >= 0,
        z >= 0,
    ensures
        count_valid_triples_for_z(k, s, z) <= k + 1,
        count_valid_triples_for_z(k, s, z) >= 0,
{
    lemma_count_for_z_helper_bounded(k, s, z, 0);
}

proof fn lemma_count_for_z_helper_bounded(k: int, s: int, z: int, y: int)
    requires
        k >= 0,
        z >= 0,
        y >= 0,
    ensures
        count_valid_triples_for_z_helper(k, s, z, y) <= k + 1 - y,
        count_valid_triples_for_z_helper(k, s, z, y) >= 0,
    decreases k + 1 - y,
{
    if y > k {
        assert(count_valid_triples_for_z_helper(k, s, z, y) == 0);
    } else {
        lemma_count_for_z_helper_bounded(k, s, z, y + 1);
        let x = s - y - z;
        let this_count = if 0 <= x <= k { 1 } else { 0 };
        assert(count_valid_triples_for_z_helper(k, s, z, y) == this_count + count_valid_triples_for_z_helper(k, s, z, y + 1));
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
/* code modified by LLM (iteration 5): Fixed runtime arithmetic to use i8 types directly instead of int conversions */
{
    let mut count: i8 = 0;
    let mut z: i8 = 0;
    
    proof {
        lemma_count_bounded(k as int, s as int);
        lemma_count_helper_bounded(k as int, s as int, 0);
    }
    
    while z <= k
        invariant
            0 <= z <= k + 1,
            0 <= count,
            count as int == count_valid_triples_helper(k as int, s as int, 0) - count_valid_triples_helper(k as int, s as int, z as int),
            count as int <= (k as int + 1) * (k as int + 1),
        decreases k - z + 1
    {
        let mut y: i8 = 0;
        let mut count_for_z: i8 = 0;
        
        proof {
            lemma_count_for_z_bounded(k as int, s as int, z as int);
            lemma_count_for_z_helper_bounded(k as int, s as int, z as int, 0);
        }
        
        while y <= k
            invariant
                0 <= z <= k,
                0 <= y <= k + 1,
                0 <= count_for_z,
                count_for_z as int == count_valid_triples_for_z_helper(k as int, s as int, z as int, 0) - count_valid_triples_for_z_helper(k as int, s as int, z as int, y as int),
                count_for_z as int <= k as int + 1,
            decreases k - y + 1
        {
            if y + z <= s && s - y - z <= k {
                let x: i8 = s - y - z;
                if 0 <= x && x <= k {
                    count_for_z = count_for_z + 1;
                }
            }
            
            proof {
                if y < k {
                    lemma_count_for_z_helper_bounded(k as int, s as int, z as int, (y + 1) as int);
                }
            }
            
            y = y + 1;
        }
        
        count = count + count_for_z;
        
        proof {
            if z < k {
                lemma_count_helper_bounded(k as int, s as int, (z + 1) as int);
            }
        }
        
        z = z + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}