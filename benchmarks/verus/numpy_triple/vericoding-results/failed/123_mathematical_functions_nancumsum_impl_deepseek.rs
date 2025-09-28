// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn seq_sum(a: Seq<i8>, start: int, end: int) -> (sum: int)
    requires
        0 <= start <= end <= a.len(),
    ensures
        sum == (sum j: int | start <= j < end; a[j] as int),
    decreases end - start,
{
    if start >= end {
        0
    } else {
        let prev = seq_sum(a, start, end - 1);
        prev + (a[end - 1] as int)
    }
}

proof fn cumulative_sum_lemma(a: Seq<i8>, i: int)
    requires
        0 <= i <= a.len(),
    ensures
        seq_sum(a, 0, i) == (if i == 0 { 0 } else { seq_sum(a, 0, i-1) + (a[i-1] as int) }),
    decreases i,
{
    if i > 0 {
        cumulative_sum_lemma(a, i - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn nancumsum(a: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == a.len(),
        a.len() > 0 ==> (result[0] as int == a[0] as int),
        forall|i: int| 0 < i < result.len() ==> result[i] as int == result[i-1] as int + a[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed implementation without calc_partial_cumsum, using proper sequence summation */
    let len = a.len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < len
        invariant
            result.len() == i,
            i <= len,
            i > 0 ==> result[0] as int == a@[0] as int,
            forall|j: int| 0 < j < i ==> result[j] as int == result[j-1] as int + a@[j] as int,
            forall|j: int| 0 <= j < i ==> result[j] as int == seq_sum(a@, 0, j+1),
        decreases len - i,
    {
        let current_val = a[i];
        if i == 0 {
            result.push(current_val);
        } else {
            let sum_prev = result[i-1];
            let new_val = (sum_prev + current_val) as i8;
            result.push(new_val);
        }
        
        proof {
            cumulative_sum_lemma(a@, (i + 1) as int);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}