// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_bit_set(x: u16, bit_index: int) -> bool
    recommends 0 <= bit_index < 10
{
    (x & (1u16 << bit_index)) != 0
}

spec fn bv10_to_seq(x: u16) -> Seq<bool> {
    seq![
        is_bit_set(x, 0), is_bit_set(x, 1), is_bit_set(x, 2), is_bit_set(x, 3),
        is_bit_set(x, 4), is_bit_set(x, 5), is_bit_set(x, 6), is_bit_set(x, 7),
        is_bit_set(x, 8), is_bit_set(x, 9)
    ]
}

spec fn array_to_bv10(arr: &[bool; 10]) -> u16
{
    array_to_bv10_helper(arr, 9)
}

spec fn array_to_bv10_helper(arr: &[bool; 10], index: nat) -> u16
    recommends index < 10
    decreases index
{
    if index == 0 {
        if arr[index as int] { 1u16 } else { 0u16 }
    } else {
        let bit: u16 = if arr[index as int] { 1u16 } else { 0u16 };
        #[verifier::truncate]
        let shifted: u16 = (bit << (index as int));
        #[verifier::truncate]
        let result: u16 = (shifted as int + array_to_bv10_helper(arr, (index - 1) as nat) as int) as u16;
        result
    }
}

fn array_to_sequence(arr: &[bool; 10]) -> (res: Vec<bool>)
    ensures res.len() == 10,
            (forall|k: int| 0 <= k < 10 ==> res[k] == arr[k]),
{
    assume(false);
    Vec::new()
}

spec fn bool_to_int(a: bool) -> int {
    if a { 1 } else { 0 }
}

spec fn xor_bool(a: bool, b: bool) -> bool {
    (a || b) && !(a && b)
}

spec fn bit_addition(s: &[bool; 10], t: &[bool; 10]) -> Seq<bool> {
    let a: u16 = array_to_bv10(s);
    let b: u16 = array_to_bv10(t);
    #[verifier::truncate]
    let c: u16 = (a as int + b as int) as u16;
    bv10_to_seq(c)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn binary_addition(s: &[bool; 10], t: &[bool; 10]) -> (sresult: Vec<bool>)
    requires s.len() == 10 && t.len() == 10
    ensures sresult.len() == 10,
            bit_addition(s, t) == sresult@,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}