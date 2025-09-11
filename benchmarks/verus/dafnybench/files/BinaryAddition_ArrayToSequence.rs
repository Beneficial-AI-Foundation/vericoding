// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn array_to_bv10(arr: Seq<bool>) -> int
    recommends arr.len() == 10
{
    array_to_bv10_helper(arr, 9)
}

spec fn array_to_bv10_helper(arr: Seq<bool>, index: int) -> int
    recommends 0 <= index < arr.len()
    decreases index
{
    if index <= 0 {
        if arr[0] { 1 } else { 0 }
    } else {
        let bit: int = if arr[index] { 1 } else { 0 };
        bit * pow2(index) + array_to_bv10_helper(arr, index - 1)
    }
}

spec fn pow2(n: int) -> int
    recommends n >= 0
    decreases n
{
    if n <= 0 { 1 } else { 2 * pow2(n - 1) }
}

spec fn is_bit_set(x: int, bit_index: int) -> bool
    recommends 0 <= bit_index < 10 && x >= 0
{
    (x / pow2(bit_index)) % 2 == 1
}

spec fn bv10_to_seq(x: int) -> Seq<bool> {
    seq![is_bit_set(x, 0), is_bit_set(x, 1), is_bit_set(x, 2), is_bit_set(x, 3),
         is_bit_set(x, 4), is_bit_set(x, 5), is_bit_set(x, 6), is_bit_set(x, 7),
         is_bit_set(x, 8), is_bit_set(x, 9)]
}

spec fn bool_to_int(a: bool) -> int {
    if a { 1 } else { 0 }
}

spec fn xor_bool(a: bool, b: bool) -> bool {
    (a || b) && !(a && b)
}

spec fn bit_addition(s: Seq<bool>, t: Seq<bool>) -> Seq<bool> 
    recommends s.len() == 10 && t.len() == 10
{
    let a: int = array_to_bv10(s);
    let b: int = array_to_bv10(t);
    let c: int = (a + b) % pow2(10);
    bv10_to_seq(c)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn array_to_sequence(arr: &[bool; 10]) -> (res: Vec<bool>)
    ensures 
        res.len() == 10,
        forall|k: int| 0 <= k < 10 ==> res[k] == arr[k]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}