// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(p: int) -> bool {
    2 <= p < 2000
}

spec fn count_primitive_roots(p: int) -> int
    recommends valid_input(p)
{
    if p == 2 { 
        1 
    } else { 
        /* Count of integers i where 1 <= i < p-1 and 
           for all j where 2 <= j <= i, not ((p-1) % j == 0 && i % j == 0) */
        Set::new(|i: int| 1 <= i < p-1 && (forall|j: int| 2 <= j <= i ==> !((p-1) % j == 0 && #[trigger] (i % j) == 0))).len() as int
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(p: i8) -> (result: i8)
    requires valid_input(p as int)
    ensures 
        result >= 0 &&
        result as int == count_primitive_roots(p as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed trailing comma in invariant block */
    if p == 2 {
        return 1;
    }
    
    let p_int = p as int;
    let mut count: i8 = 0;
    let mut i: i8 = 1;
    
    while i < p - 1
        invariant
            2 <= p_int < 2000,
            p_int == p as int,
            1 <= i as int,
            i as int <= p_int - 1,
            0 <= count as int,
            count as int == Set::new(|k: int| 1 <= k < i as int && (forall|j: int| 2 <= j <= k ==> !((p_int - 1) % j == 0 && k % j == 0))).len() as int
        decreases (p as int - 1) - i as int
    {
        let mut has_common_divisor = false;
        let mut j: i8 = 2;
        
        while j <= i
            invariant
                2 <= p_int < 2000,
                p_int == p as int,
                1 <= i as int,
                i as int < p_int - 1,
                2 <= j as int,
                j as int <= i as int + 1,
                has_common_divisor == (exists|k: int| 2 <= k < j as int && (p_int - 1) % k == 0 && i as int % k == 0)
            decreases i as int - j as int + 1
        {
            if (p - 1) % j == 0 && i % j == 0 {
                has_common_divisor = true;
                break;
            }
            j = j + 1;
        }
        
        if !has_common_divisor {
            count = count + 1;
        }
        
        i = i + 1;
    }
    
    count
}
// </vc-code>


}

fn main() {}