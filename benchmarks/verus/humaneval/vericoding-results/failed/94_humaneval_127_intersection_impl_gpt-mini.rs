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
/* helper modified by LLM (iteration 5): prove int to nat round-trip for nonnegative ints */
fn int_to_nat_identity(a: int)
    requires a >= 0,
    ensures (a as nat) as int == a,
{
    assert((a as nat) as int == a);
}

// </vc-helpers>

// <vc-spec>
fn intersection(start1: i8, end1: i8, start2: i8, end2: i8) -> (result: String)
    requires start1 as int <= end1 as int && start2 as int <= end2 as int,
    ensures (result@ =~= seq!['Y', 'E', 'S'] || result@ =~= seq!['N', 'O']) && (result@ =~= seq!['Y', 'E', 'S'] <==> (max(start1 as int, start2 as int) <= min(end1 as int, end2 as int) && is_prime((min(end1 as int, end2 as int) - max(start1 as int, start2 as int) + 1) as nat))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): add decreases clause to loop */
    let s1 = start1 as i64;
    let e1 = end1 as i64;
    let s2 = start2 as i64;
    let e2 = end2 as i64;
    let os = if s1 >= s2 { s1 } else { s2 };
    let oe = if e1 <= e2 { e1 } else { e2 };
    if os <= oe {
        let len_i64 = oe - os + 1;
        proof {
            assert(len_i64 >= 0);
            let s1_int: int = start1 as int;
            let e1_int: int = end1 as int;
            let s2_int: int = start2 as int;
            let e2_int: int = end2 as int;
            let os_int = max(s1_int, s2_int);
            let oe_int = min(e1_int, e2_int);
            assert(os_int <= oe_int);
            let _len_int = oe_int - os_int + 1;
            assert(_len_int >= 0);
        }
        if len_i64 <= 1 {
            String::from_str("NO")
        } else {
            let mut d: i64 = 2;
            let mut is_p = true;
            while d < len_i64
                invariant
                    2 <= d,
                    d <= len_i64,
                decreases (len_i64 - d) as nat
            {
                if len_i64 % d == 0 {
                    is_p = false;
                    break;
                }
                d += 1;
            }
            if is_p {
                String::from_str("YES")
            } else {
                String::from_str("NO")
            }
        }
    } else {
        String::from_str("NO")
    }
}

// </vc-code>


}

fn main() {}