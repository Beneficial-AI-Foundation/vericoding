// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(input: Seq<char>) -> bool {
    input.len() > 0 &&
    (exists|i: int| 0 <= i < input.len() && input[i] == ' ') &&
    (forall|j: int| 0 <= j < input.len() ==> 
        ('0' <= input[j] <= '9' || input[j] == ' ' || input[j] == '\n'))
}

spec fn gcd(a: nat, b: nat) -> nat 
    decreases a + b
{
    if a == 0 { b }
    else if b == 0 { a }
    else if a > b { gcd((a - b) as nat, b) }
    else { gcd(a, (b - a) as nat) }
}

#[verifier::opaque]
spec fn f_mathematical(x: nat, y: nat) -> nat
    decreases y
{
    y / 2
}

spec fn valid_output(result: Seq<char>) -> bool {
    result.len() > 0 &&
    (forall|i: int| 0 <= i < result.len() ==> 
        ('0' <= result[i] <= '9' || result[i] == '\n')) &&
    result[result.len() - 1] == '\n'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<char>) -> (result: Vec<char>)
    requires valid_input(input@)
    ensures valid_output(result@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}