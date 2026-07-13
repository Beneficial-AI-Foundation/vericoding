// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_nonzero_digits(n: nat) -> nat
    decreases n
{
    if n == 0 { 0 }
    else { 
        let digit = n % 10;
        let rest_count = count_nonzero_digits(n / 10);
        if digit == 0 { rest_count } else { rest_count + 1 }
    }
}

spec fn is_classy_number(n: nat) -> bool {
    count_nonzero_digits(n) <= 3
}

fn is_classy_number_impl(n: u64) -> (result: bool)
    ensures result == is_classy_number(n as nat)
{
    // impl-start
    assume(false);
    false
    // impl-end
}

fn count_classy_integers(start: u64, finish: u64) -> (result: u64)
    requires start <= finish,
    ensures 
        result >= 0,
        result <= finish - start + 1,
        start > finish ==> result == 0,
        start == finish ==> result == (if is_classy_number(start as nat) { 1u64 } else { 0u64 })
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-spec>
// <vc-code>
// </vc-code>


}
fn main() {
    // let test_cases = vec![(1, 1000), (1024, 1024), (65536, 65536), (999999, 1000001)];
    // for (l, r) in test_cases {
    //     let count = count_classy_integers(l, r);
    //     println!("{}", count);
    // }
}