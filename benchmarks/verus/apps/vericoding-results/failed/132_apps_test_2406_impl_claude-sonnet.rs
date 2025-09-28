// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, heights: Seq<int>) -> bool {
    n > 0 && heights.len() == n &&
    (forall|i: int| 0 <= i < n ==> #[trigger] heights[i] >= 0) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] heights[i] < heights[i+1])
}

spec fn valid_output(n: int, result: Seq<int>) -> bool {
    result.len() == n &&
    (forall|i: int| 0 <= i < n ==> #[trigger] result[i] >= 0) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] result[i] <= result[i+1]) &&
    (forall|i: int| 0 <= i < n-1 ==> #[trigger] result[i+1] - result[i] <= 1)
}

spec fn is_stable(result: Seq<int>) -> bool {
    forall|i: int| 0 <= i < result.len()-1 ==> !(#[trigger] result[i] + 2 <= result[i+1])
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added trigger annotations for quantifiers */
proof fn lemma_sum_seq_subrange(s: Seq<int>, i: int, j: int)
    requires 0 <= i <= j <= s.len()
    ensures sum_seq(s.subrange(i, j)) >= 0
    decreases j - i
{
    if i == j {
        assert(s.subrange(i, j).len() == 0);
    } else {
        lemma_sum_seq_subrange(s, i + 1, j);
    }
}

proof fn lemma_valid_output_implies_stable(n: int, result: Seq<int>)
    requires valid_output(n, result)
    ensures is_stable(result)
{
    if n > 1 {
        assert(forall|i: int| 0 <= i < n-1 ==> #[trigger] result[i+1] - result[i] <= 1);
        assert(forall|i: int| 0 <= i < n-1 ==> !(#[trigger] result[i] + 2 <= result[i+1]));
    }
}

proof fn lemma_sum_preservation(old_seq: Seq<int>, new_seq: Seq<int>, pos: int, old_val: int, new_val: int)
    requires
        0 <= pos < old_seq.len(),
        old_seq.len() == new_seq.len(),
        old_seq[pos] == old_val,
        new_seq[pos] == new_val,
        forall|i: int| 0 <= i < old_seq.len() && i != pos ==> #[trigger] old_seq[i] == new_seq[i]
    ensures
        sum_seq(new_seq) == sum_seq(old_seq) - old_val + new_val
    decreases old_seq.len()
{
    if old_seq.len() == 1 {
        assert(pos == 0);
    } else if pos == 0 {
        assert(sum_seq(old_seq) == old_val + sum_seq(old_seq.subrange(1, old_seq.len() as int)));
        assert(sum_seq(new_seq) == new_val + sum_seq(new_seq.subrange(1, new_seq.len() as int)));
    } else {
        lemma_sum_preservation(old_seq.subrange(1, old_seq.len() as int), new_seq.subrange(1, new_seq.len() as int), pos - 1, old_val, new_val);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, heights: Vec<i8>) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, heights@.map(|i, v| v as int))
    ensures 
        valid_output(n as int, result@.map(|i, v| v as int)) &&
        sum_seq(result@.map(|i, v| v as int)) == sum_seq(heights@.map(|i, v| v as int)) &&
        is_stable(result@.map(|i, v| v as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added trigger annotations for loop invariant */
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result@[j] as int >= 0,
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] result@[j] as int <= result@[j+1] as int,
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] result@[j+1] as int - result@[j] as int <= 1
        decreases n - i
    {
        let prev_height = if i == 0 { 0 } else { result[i as usize - 1] };
        let current_height = heights[i as usize];
        
        let new_height = if prev_height + 1 >= current_height {
            prev_height + 1
        } else {
            current_height
        };
        
        result.push(new_height);
        i = i + 1;
    }
    
    proof {
        lemma_valid_output_implies_stable(n as int, result@.map(|i, v| v as int));
    }
    
    result
}
// </vc-code>


}

fn main() {}