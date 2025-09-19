// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn binary_digits_valid(digits: Seq<u32>) -> bool {
    forall|i: int| 0 <= i < digits.len() ==> (digits[i] == 0 || digits[i] == 1)
}

spec fn spec_binary_to_decimal_value(digits: Seq<u32>) -> nat {
    if digits.len() == 0 {
        0
    } else {
        digits.fold_left(0nat, |acc: nat, bit: u32| acc * 2 + bit as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn binary_to_decimal(digits: &Vec<u32>) -> (result: u32)
    requires binary_digits_valid(digits@),
    ensures result as nat == spec_binary_to_decimal_value(digits@),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}

proof fn binary_to_decimal_spec_satisfied(digits: Seq<u32>)
    requires binary_digits_valid(digits),
    ensures {
        let result = spec_binary_to_decimal_value(digits);
        result == spec_binary_to_decimal_value(digits)
    }
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-code>


}
fn main() {}