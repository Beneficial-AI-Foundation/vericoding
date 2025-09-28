// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_prime(n: nat) -> bool {
    n > 1 &&
    forall|k: nat| #[trigger] (n % k) != 0 ==> 2 <= k < n
}

spec fn min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn intersection(start1: i8, end1: i8, start2: i8, end2: i8) -> (result: String)
    requires start1 as int <= end1 as int && start2 as int <= end2 as int,
    ensures (result@ =~= seq!['Y', 'E', 'S'] || result@ =~= seq!['N', 'O']) && (result@ =~= seq!['Y', 'E', 'S'] <==> (max(start1 as int, start2 as int) <= min(end1 as int, end2 as int) && is_prime((min(end1 as int, end2 as int) - max(start1 as int, start2 as int) + 1) as nat))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use new_strlit! macro to create String literals */
    let s1_i8 = if start1 >= start2 { start1 } else { start2 };
    let e1_i8 = if end1 <= end2 { end1 } else { end2 };
    
    if s1_i8 <= e1_i8 {
        let length_i8: i8 = e1_i8 - s1_i8 + 1;
        
        proof {
            assert(s1_i8 as int == max(start1 as int, start2 as int));
            assert(e1_i8 as int == min(end1 as int, end2 as int));
            assert(length_i8 as int == e1_i8 as int - s1_i8 as int + 1);
        }
        
        if length_i8 <= 1 {
            return new_strlit!("NO");
        }
        
        let mut k: i8 = 2;
        let mut is_prime_flag = true;
        
        while k < length_i8
            invariant
                2 <= k <= length_i8,
                length_i8 as int == e1_i8 as int - s1_i8 as int + 1,
                is_prime_flag <==> forall|j: nat| 2 <= j < k as nat ==> #[trigger] ((length_i8 as nat) % j) != 0,
            decreases length_i8 - k
        {
            if length_i8 % k == 0 {
                is_prime_flag = false;
                break;
            }
            k = k + 1;
        }
        
        proof {
            if is_prime_flag {
                assert(forall|j: nat| 2 <= j < length_i8 as nat ==> #[trigger] ((length_i8 as nat) % j) != 0);
                assert(length_i8 > 1);
                assert(is_prime(length_i8 as nat));
            }
        }
        
        if is_prime_flag {
            return new_strlit!("YES");
        } else {
            return new_strlit!("NO");
        }
    } else {
        return new_strlit!("NO");
    }
}
// </vc-code>


}

fn main() {}