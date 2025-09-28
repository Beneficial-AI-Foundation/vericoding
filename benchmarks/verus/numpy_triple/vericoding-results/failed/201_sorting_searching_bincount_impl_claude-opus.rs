// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 4): Track actual count separately from capped value */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i <= max_val as usize
        invariant
            i <= max_val as usize + 1,
            result.len() == i,
            forall|val: int| 0 <= val < i ==> result[val] as nat == count_occurrences(x@.map(|k: int, v: u8| v as nat), val as nat),
        decreases max_val as usize + 1 - i
    {
        let mut actual_count: usize = 0;
        let mut j: usize = 0;
        while j < x.len()
            invariant
                j <= x.len(),
                actual_count == count_occurrences(x@.take(j as int).map(|k: int, v: u8| v as nat), i as nat),
            decreases x.len() - j
        {
            if x[j] as usize == i {
                actual_count = actual_count + 1;
            }
            j = j + 1;
        }
        assert(x@.take(x.len() as int) == x@);
        let capped_count: u8 = if actual_count > 255 { 255 } else { actual_count as u8 };
        result.push(capped_count);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}