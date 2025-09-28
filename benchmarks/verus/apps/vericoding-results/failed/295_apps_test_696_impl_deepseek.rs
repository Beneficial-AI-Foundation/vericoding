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
/* helper modified by LLM (iteration 5): Fixed type conversion issues by using proper ghost variables */
proof fn divides(a: int, b: int) -> bool
    requires b != 0
    ensures result == (a % b == 0)
{
    a % b == 0
}

proof fn lemma_positive_mod(a: int, b: int)
    requires
        b != 0,
        a >= 0
    ensures
        0 <= a % b < b
{
}
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
    /* code modified by LLM (iteration 5): Fixed type conversion errors by using ghost variables */
    if p == 2 {
        return 1;
    }
    
    let ghost p_int = p as int;
    let ghost p_minus_1 = p_int - 1;
    let mut count: i8 = 0;
    let mut i: i8 = 1;
    
    while i < p - 1
        invariant
            count >= 0,
            i >= 1,
            i <= p - 1,
            count as int == Set::new(|j: int| 1 <= j < i as int && 
                (forall|k: int| 2 <= k <= j ==> !(divides(p_minus_1, k) && divides(j, k)))).len() as int
    {
        let ghost i_int = i as int;
        let mut has_common_divisor = false;
        
        let mut j: i8 = 2;
        while j <= i
            invariant
                j >= 2,
                j <= i + 1,
                has_common_divisor ==> (exists|k: int| 2 <= k <= i_int && divides(p_minus_1, k) && divides(i_int, k)),
                !has_common_divisor ==> (forall|k: int| 2 <= k < j as int ==> !(divides(p_minus_1, k) && divides(i_int, k)))
        {
            let ghost j_int = j as int;
            if p_minus_1 % j_int == 0 && i_int % j_int == 0 {
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