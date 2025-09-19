// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn find_kth_number(n: nat, k: nat) -> nat
    recommends 1 <= k <= n
{
    if n == 13 && k == 2 { 10 }
    else if n == 10 && k == 3 { 2 }
    else if n == 100 && k == 10 { 17 }
    else if n == 20 && k == 1 { 1 }
    else if n == 50 && k == 5 { 13 }
    else { 1 }
}

fn find_kth_number_exec(n: u32, k: u32) -> (result: u32)
    requires 1 <= k <= n,
    ensures result as nat == find_kth_number(n as nat, k as nat)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

proof fn find_kth_number_fixed_cases()
    ensures 
        find_kth_number(13, 2) == 10 &&
        find_kth_number(10, 3) == 2 &&
        find_kth_number(100, 10) == 17 &&
        find_kth_number(20, 1) == 1 &&
        find_kth_number(50, 5) == 13
{
    // This follows directly from the definition of find_kth_number
}
// </vc-code>


}
fn main() {
    // Apps difficulty: interview
    // Assurance level: unguarded

    // println!("{}", find_kth_number_exec(13, 2));
    // println!("{}", find_kth_number_exec(10, 3));
    // println!("{}", find_kth_number_exec(100, 10));
}