// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove unsupported contains call and add helper for sequence membership */
spec fn count_rec(a: Seq<int>, x: int) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0int
    } else {
        count_rec(a.subrange(1, a.len() as int), x) + (if a[0] == x { 1int } else { 0int })
    }
}

spec fn contains_seq(seq: Seq<int>, x: int) -> bool
    decreases seq.len()
{
    if seq.len() == 0 {
        false
    } else {
        seq[0] == x || contains_seq(seq.subrange(1, seq.len() as int), x)
    }
}
// </vc-helpers>

// <vc-spec>
fn remove_duplicates(a: Vec<i8>) -> (result: Vec<i8>)
    requires 
        forall|i: int| 0 <= i < a@.len() ==> count_rec(a@.map(|_i: int, x: i8| x as int), a@[i] as int) >= 1
    ensures 
        forall|i: int| 0 <= i < result@.len() ==> count_rec(a@.map(|_i: int, x: i8| x as int), result@[i] as int) == 1,
        forall|i: int| 0 <= i < a@.len() ==> (result@.map(|_i: int, x: i8| x as int).contains(a@[i] as int) <==> count_rec(a@.map(|_i: int, x: i8| x as int), a@[i] as int) == 1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replace contains with custom helper function */
{
    let mut result = Vec::new();
    let mut seen = Vec::new();
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < result@.len() ==> count_rec(a@.map(|_k: int, y: i8| y as int), result@[j] as int) == 1,
            forall|j: int| 0 <= j < a@.len() ==> (if contains_seq(result@.map(|_k: int, val: i8| val as int), a@[j] as int) {
                count_rec(a@.map(|_k: int, val: i8| val as int), a@[j] as int) == 1
            } else {
                count_rec(a@.map(|_k: int, val: i8| val as int), a@[j] as int) != 1
            }),
            seen@.len() == result@.len(),
            forall|k: int| 0 <= k < seen@.len() ==> seen@[k] == result@[k]
        decreases a.len() - i
    {
        let current = a[i];
        if !contains_seq(seen@.map(|_idx: int, x: i8| x as int), current as int) {
            result.push(current);
            seen.push(current);
        }
        i += 1;
    }
    
    result
}
// </vc-code>


}

fn main() {}