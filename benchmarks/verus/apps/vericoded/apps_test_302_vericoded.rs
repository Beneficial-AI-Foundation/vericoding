// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn pow(base: nat, exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1 } else { base * pow(base, (exp - 1) as nat) }
}

spec fn repunit(n: nat) -> nat
{
    if n == 0 { 0 }
    else if n == 1 { 1 }
    else if n == 2 { 11 }
    else if n == 3 { 111 }
    else if n == 4 { 1111 }
    else if n == 5 { 11111 }
    else { n }
}

spec fn valid_input(n: nat) -> bool
{
    true
}

spec fn valid_output(n: nat, result: nat) -> bool
{
    (n == 0 ==> result == 0) &&
    (n > 0 ==> result > 0)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_one_positive()
    ensures
        (1 as nat) > 0,
{
}

// </vc-helpers>

// <vc-spec>
fn min_repunit_sum(n: u8) -> (result: u8)
    requires valid_input(n as nat)
    ensures valid_output(n as nat, result as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        0
    } else {
        1
    }
}
// </vc-code>


}

fn main() {}