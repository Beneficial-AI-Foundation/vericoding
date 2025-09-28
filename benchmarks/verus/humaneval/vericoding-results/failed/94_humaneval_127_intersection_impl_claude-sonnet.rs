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
/* helper modified by LLM (iteration 5): added decreases clause to while loop */
fn exec_max(a: i8, b: i8) -> (result: i8)
    requires
        true,
    ensures
        result as int == max(a as int, b as int),
{
    if a >= b { a } else { b }
}

fn exec_min(a: i8, b: i8) -> (result: i8)
    requires
        true,
    ensures
        result as int == min(a as int, b as int),
{
    if a <= b { a } else { b }
}

fn exec_is_prime(n: i8) -> (result: bool)
    requires
        n >= 1,
    ensures
        result == is_prime(n as nat),
{
    if n <= 1 {
        return false;
    }
    let mut k = 2;
    while k < n
        invariant
            2 <= k <= n,
            forall|j: int| 2 <= j < k ==> (n as int) % j != 0,
        decreases n - k
    {
        if n % k == 0 {
            return false;
        }
        k = k + 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
fn intersection(start1: i8, end1: i8, start2: i8, end2: i8) -> (result: String)
    requires start1 as int <= end1 as int && start2 as int <= end2 as int,
    ensures (result@ =~= seq!['Y', 'E', 'S'] || result@ =~= seq!['N', 'O']) && (result@ =~= seq!['Y', 'E', 'S'] <==> (max(start1 as int, start2 as int) <= min(end1 as int, end2 as int) && is_prime((min(end1 as int, end2 as int) - max(start1 as int, start2 as int) + 1) as nat))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed in main implementation */
    let intersection_start = exec_max(start1, start2);
    let intersection_end = exec_min(end1, end2);
    
    if intersection_start <= intersection_end {
        let length = intersection_end - intersection_start + 1;
        if exec_is_prime(length) {
            "YES".to_string()
        } else {
            "NO".to_string()
        }
    } else {
        "NO".to_string()
    }
}
// </vc-code>


}

fn main() {}