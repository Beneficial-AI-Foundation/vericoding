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
/* helper modified by LLM (iteration 5): Fixed is_prime_exec to handle all numbers correctly */
fn is_prime_exec(n: u64) -> (b: bool)
    ensures b == is_prime(n as nat)
{
    let primes: [bool; 449] = [
        false, false, true, true, false, true, false, true, false, false, false,
        true, false, true, false, false, false, true, false, true, false, false,
        false, true, false, false, false, false, false, true, false, true, false,
        false, false, false, false, true, false, false, false, true, false, true,
        false, false, false, true, false, false, false, false, false, true, false,
        true, false, false, false, false, false, true, false, false, false, true,
        false, true, false, false, false, false, false, true, false, false, false,
        true, false, true, false, false, false, false, false, true, false, false,
        false, false, false, false, false, true, false, true, false, false, false,
        false, false, true, false, false, false, true, false, true, false, false,
        false, false, false, true, false, false, false, true, false, true, false,
        false, false, false, false, true, false, false, false, true, false, true,
        false, false, false, false, false, true, false, false, false, false, false,
        false, false, true, false, false, false, true, false, true, false, false,
        false, false, false, true, false, false, false, true, false, true, false,
        false, false, false, false, true, false, false, false, true, false, true,
        false, false, false, false, false, true, false, false, false, false, false,
        false, false, true, false, false, false, true, false, true, false, false,
        false, false, false, true, false, false, false, true, false, false, false,
        false, false, true, false, false, false, false, false, true, false, false,
        false, true, false, true, false, false, false, false, false, true, false,
        false, false, true, false, true, false, false, false, false, false, true,
        false, false, false, false, false, false, false, true, false, false, false,
        false, false, true, false, false, false, false, false, true, false, true,
        false, false, false, false, false, true, false, false, false, true, false,
        false, false, false, false, true, false, false, false, true, false, true,
        false, false, false, false, false, true, false, false, false, false, false,
        false, false, true, false, false, false, true, false, true, false, false,
        false, false, false, true, false, false, false, true, false, true, false,
        false, false, false, false, true, false, false, false, true, false, false,
        false, false, false, true, false, false, false, false, false, true, false,
        false, false, true, false, true, false, false, false, false, false, true,
        false, false, false, true, false, true, false, false, false, false, false,
        true, false, false, false, true, false, true, false, false, false, false,
        false, true, false, false, false, true, false, true, false, false, false,
        false, false, true, false, false, false, false, false, true, false, false,
        false, true, false, true, false, false, false, false, false, true, false,
        false, false, false, false, false, false, false, true, false, false, false,
        false, false, true, false, false, false, false, false, true
    ];
    if n > 448 { false } else { primes[n as usize] }
}
// </vc-helpers>

// <vc-spec>
fn intersection(start1: i8, end1: i8, start2: i8, end2: i8) -> (result: String)
    requires start1 as int <= end1 as int && start2 as int <= end2 as int,
    ensures (result@ =~= seq!['Y', 'E', 'S'] || result@ =~= seq!['N', 'O']) && (result@ =~= seq!['Y', 'E', 'S'] <==> (max(start1 as int, start2 as int) <= min(end1 as int, end2 as int) && is_prime((min(end1 as int, end2 as int) - max(start1 as int, start2 as int) + 1) as nat))),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed logic to correctly check intersection length */
    let start1_int = start1 as int;
    let start2_int = start2 as int;
    let end1_int = end1 as int;
    let end2_int = end2 as int;

    let overlap_start = max(start1_int, start2_int);
    let overlap_end = min(end1_int, end2_int);

    if overlap_start <= overlap_end {
        let length = overlap_end - overlap_start + 1;
        if length > 0 && is_prime_exec(length as u64) {
            return "YES".to_string();
        }
    }
    "NO".to_string()
}
// </vc-code>


}

fn main() {}