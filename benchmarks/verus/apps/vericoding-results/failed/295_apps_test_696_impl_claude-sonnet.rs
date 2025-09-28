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
/* helper modified by LLM (iteration 5): fixed lemma syntax */
spec fn is_coprime(a: int, b: int) -> bool {
    gcd(a, b) == 1
}

spec fn gcd(a: int, b: int) -> int
    recommends a >= 0 && b >= 0
    decreases a + b
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a <= b {
        gcd(a, b - a)
    } else {
        gcd(a - b, b)
    }
}

spec fn euler_phi(n: int) -> int
    recommends n >= 1
{
    Set::new(|i: int| 1 <= i < n && is_coprime(i, n)).len() as int
}

proof fn lemma_primitive_roots_eq_euler_phi(p: int)
    requires valid_input(p)
    ensures count_primitive_roots(p) == if p == 2 { 1 } else { euler_phi(p - 1) }
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
/* code modified by LLM (iteration 5): fixed trigger annotation syntax */
{
    if p == 2 {
        1
    } else {
        let mut count = 0i8;
        let mut i = 1i8;
        
        while i < p - 1
            invariant
                1 <= i <= p - 1,
                count >= 0,
            decreases p - 1 - i
        {
            let mut is_primitive = true;
            let mut j = 2i8;
            
            while j <= i && is_primitive
                invariant
                    2 <= j <= i + 1,
                    is_primitive ==> (forall|k: int| 2 <= k < j ==> !((p as int - 1) % k == 0 && (i as int) % k == 0)),
                decreases i + 1 - j
            {
                if (p - 1) % j == 0 && i % j == 0 {
                    is_primitive = false;
                }
                j = j + 1;
            }
            
            if is_primitive {
                count = count + 1;
            }
            
            i = i + 1;
        }
        
        count
    }
}
// </vc-code>


}

fn main() {}