// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, k: int) -> bool
{
    n > 0 && k > 0
}

spec fn is_strictly_increasing(s: Seq<int>) -> bool
{
    forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] < s[i+1]
}

spec fn all_positive(s: Seq<int>) -> bool
{
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] > 0
}

spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_seq(s.subrange(1, s.len() as int)) }
}

spec fn valid_sequence(s: Seq<int>, n: int, k: int) -> bool
{
    s.len() == k && all_positive(s) && is_strictly_increasing(s) && sum_seq(s) == n
}

spec fn is_possible(n: int, k: int) -> bool
{
    k * (k + 1) / 2 <= n
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added lemma keyword to fix syntax error */
lemma lemma_sum_seq_property(s: Seq<int>)
    requires s.len() > 0
    ensures sum_seq(s) == s[0] + sum_seq(s.subrange(1, s.len() as int))
{
}

lemma lemma_sum_seq_append(s1: Seq<int>, s2: Seq<int>)
    ensures sum_seq(s1 + s2) == sum_seq(s1) + sum_seq(s2)
    decreases s1.len()
{
    if s1.len() == 0 {
    } else {
        lemma_sum_seq_property(s1 + s2);
        lemma_sum_seq_append(s1.subrange(1, s1.len() as int), s2);
    }
}

lemma lemma_sum_arithmetic_sequence(start: int, len: int)
    requires
        start > 0,
        len > 0
    ensures sum_seq(Seq::new(len, |i: int| start + i)) == len * start + len * (len - 1) / 2
    decreases len
{
    if len == 1 {
    } else {
        let s = Seq::new(len, |i: int| start + i);
        let s_tail = Seq::new(len - 1, |i: int| start + 1 + i);
        assert(s.subrange(1, len) == s_tail);
        lemma_sum_arithmetic_sequence(start + 1, len - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8, k: i8) -> (result: Vec<i8>)
    requires 
        valid_input(n as int, k as int)
    ensures 
        ((result.len() == 1 && result[0] == -1) || 
         (valid_sequence(result@.map(|_i: int, x: i8| x as int), n as int, k as int))) &&
        ((result.len() == 1 && result[0] == -1) <==> !is_possible(n as int, k as int))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed logic to properly handle sequence construction and verification */
    let min_sum = k * (k + 1) / 2;
    if n < min_sum {
        let mut result = Vec::new();
        result.push(-1);
        return result;
    }
    
    let mut result = Vec::new();
    let mut i = 0;
    while i < k
        invariant
            0 <= i <= k,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == j + 1
    {
        result.push((i + 1) as i8);
        i += 1;
    }
    
    let current_sum = k * (k + 1) / 2;
    let diff = n - current_sum;
    let last_idx = (k - 1) as usize;
    result.set(last_idx, result[last_idx] + diff as i8);
    
    proof {
        let final_seq = result@.map(|_i: int, x: i8| x as int);
        assert(final_seq.len() == k);
        assert(forall|j: int| 0 <= j < k - 1 ==> final_seq[j] == j + 1);
        assert(final_seq[k - 1] == k + diff);
        assert(all_positive(final_seq));
        assert(is_strictly_increasing(final_seq));
        assert(sum_seq(final_seq) == n);
    }
    
    result
}
// </vc-code>


}

fn main() {}