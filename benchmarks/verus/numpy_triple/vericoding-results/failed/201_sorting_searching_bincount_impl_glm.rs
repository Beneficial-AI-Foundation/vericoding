// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed return type from nat to usize for executable use */
fn count_occurrences_in_vec(x: Vec<u8>, val: u8) -> (count: usize)
    ensures count as nat == count_occurrences(x@.map(|i: int, v: u8| v as nat), val as nat),
{
    let mut count: usize = 0;
    for i in 0..x.len()
        invariant
            0 <= i <= x.len(),
            count as nat == count_occurrences(x@.subrange(0, i as int).map(|i: int, v: u8| v as nat), val as nat),
        decreases x.len() - i
    {
        if x[i] == val {
            count += 1;
        }
    }
    count
}
// </vc-helpers>

// <vc-spec>
spec fn count_occurrences(x: Seq<nat>, val: nat) -> nat {
    x.filter(|v: nat| v == val).len()
}

fn numpy_bincount(x: Vec<u8>, max_val: u8) -> (result: Vec<u8>)
    requires 
        forall|i: int| 0 <= i < x.len() ==> x[i] as nat <= max_val as nat,
    ensures
        result.len() == max_val as nat + 1,
        forall|val: int| 0 <= val <= max_val as int ==> 
            result[val] as nat == count_occurrences(x@.map(|i: int, v: u8| v as nat), val as nat),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): changed inclusive range to exclusive range to fix compilation error */
{
    let mut result = Vec::<u8>::with_capacity(max_val as usize + 1);
    for val in 0..(max_val as usize + 1)
        invariant
            val <= max_val as usize + 1,
            result.len() == val,
            forall|i: int| 0 <= i < val as int ==> 
                result[i] as nat == count_occurrences(x@.map(|i: int, v: u8| v as nat), i as nat),
    {
        let val_u8 = val as u8;
        let count = count_occurrences_in_vec(x, val_u8);
        result.push(count as u8);
    }
    result
}
// </vc-code>


}
fn main() {}