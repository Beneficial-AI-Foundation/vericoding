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
/* helper modified by LLM (iteration 5): Fix let pattern binding in ensures clause and int/nat usage */
fn compute_intersection(start1: i8, start2: i8, end1: i8, end2: i8) -> (result: (i8, i8))
    requires start1 <= end1 && start2 <= end2,
    ensures
        result.0 == (if start1 > start2 { start1 } else { start2 }),
        result.1 == (if end1 < end2 { end1 } else { end2 }),
        result.0 <= result.1,
{
    let s = if start1 > start2 { start1 } else { start2 };
    let e = if end1 < end2 { end1 } else { end2 };
    (s, e)
}

proof fn intersection_is_prime_lemma(start1: int, start2: int, end1: int, end2: int)
    requires
        start1 <= end1,
        start2 <= end2,
    ensures
        min(end1, end2) - max(start1, start2) + 1 >= 0,
{
    assert(max(start1, start2) <= min(end1, end2)) ==> (min(end1, end2) - max(start1, start2) + 1 >= 1);
    assert(max(start1, start2) > min(end1, end2)) ==> (min(end1, end2) - max(start1, start2) + 1 <= 0);
}

fn check_prime(n: nat) -> (result: bool)
    requires n > 0,
    ensures result == is_prime(n),
{
    if n <= 1 {
        false
    } else {
        let mut divisor = 2;
        while divisor < n
            invariant
                2 <= divisor <= n,
                forall|k: nat| 2 <= k < divisor ==> #[trigger] (n % k) != 0,
            decreases n - divisor,
        {
            if n % divisor == 0 {
                return false;
            }
            divisor += 1;
        }
        true
    }
}
// </vc-helpers>

// <vc-spec>
fn intersection(start1: i8, end1: i8, start2: i8, end2: i8) -> (result: String)
    requires start1 as int <= end1 as int && start2 as int <= end2 as int,
    ensures (result@ =~= seq!['Y', 'E', 'S'] || result@ =~= seq!['N', 'O']) && (result@ =~= seq!['Y', 'E', 'S'] <==> (max(start1 as int, start2 as int) <= min(end1 as int, end2 as int) && is_prime((min(end1 as int, end2 as int) - max(start1 as int, start2 as int) + 1) as nat))),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix int/nat conversion errors and ensure type safety */
{
    let (intersect_start, intersect_end) = compute_intersection(start1, start2, end1, end2);
    
    if intersect_start <= intersect_end {
        proof {
            intersection_is_prime_lemma(start1 as int, start2 as int, end1 as int, end2 as int);
        }
        
        let length_nat = (intersect_end - intersect_start + 1) as nat;
        
        if length_nat > 0 {
            let is_prime_length = check_prime(length_nat);
            
            if is_prime_length {
                String::from_str("YES")
            } else {
                String::from_str("NO")
            }
        } else {
            String::from_str("NO")
        }
    } else {
        String::from_str("NO")
    }
}
// </vc-code>


}

fn main() {}