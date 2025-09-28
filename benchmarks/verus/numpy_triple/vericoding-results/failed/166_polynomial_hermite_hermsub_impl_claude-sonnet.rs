// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Replaced wrapping_neg with manual implementation using wrapping_sub */
fn safe_i8_sub(a: i8, b: i8) -> (result: i8)
    ensures
        result as int == (a as int) - (b as int),
{
    a.wrapping_sub(b)
}

fn safe_i8_neg(a: i8) -> (result: i8)
    ensures
        result as int == -(a as int),
{
    0i8.wrapping_sub(a)
}
// </vc-helpers>

// <vc-spec>
fn hermsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < c1.len() && 0 <= i < c2.len() ==> 
            result@[i] == c1@[i] - c2@[i],
        c1.len() > c2.len() ==> forall|i: int| 
            c2.len() <= i < c1.len() ==> result@[i] == c1@[i],
        c2.len() > c1.len() ==> forall|i: int| 
            c1.len() <= i < c2.len() ==> result@[i] == -c2@[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop structure and bounds checking */
    let min_len = if c1.len() <= c2.len() { c1.len() } else { c2.len() };
    let max_len = if c1.len() >= c2.len() { c1.len() } else { c2.len() };
    let mut result = Vec::with_capacity(max_len);
    
    let mut i = 0;
    while i < min_len
        invariant
            i <= min_len,
            min_len <= max_len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == c1@[j] - c2@[j],
        decreases min_len - i
    {
        let val1 = c1[i];
        let val2 = c2[i];
        result.push(safe_i8_sub(val1, val2));
        i += 1;
    }
    
    while i < c1.len()
        invariant
            min_len <= i <= c1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < min_len ==> result@[j] == c1@[j] - c2@[j],
            forall|j: int| min_len <= j < i ==> result@[j] == c1@[j],
        decreases c1.len() - i
    {
        result.push(c1[i]);
        i += 1;
    }
    
    while i < c2.len()
        invariant
            min_len <= i <= c2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < min_len ==> result@[j] == c1@[j] - c2@[j],
            forall|j: int| min_len <= j < i ==> result@[j] == -c2@[j],
        decreases c2.len() - i
    {
        let val = c2[i];
        result.push(safe_i8_neg(val));
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}