// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate decode_rle definition and fixed helper functions */
proof fn lemma_seq_index_len<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s[i] == s[i],
{
}

spec fn spec_sum(s: Seq<usize>) -> int {
    if s.len() == 0 {
        0
    } else {
        s[0] as int + spec_sum(s.subrange(1, s.len() as int))
    }
}

proof fn lemma_seq_empty() -> (s: Seq<char>)
    ensures
        s == Seq::empty(),
{
    Seq::empty()
}

proof fn lemma_seq_push<T>(s: Seq<T>, x: T)
    ensures
        s.push(x) == s.push(x),
{
}

proof fn lemma_seq_ext_equal<T>(s1: Seq<T>, s2: Seq<T>)
    requires
        s1 =~= s2,
    ensures
        s1 == s2,
{
}
// </vc-helpers>

// <vc-spec>
fn run_length_encode(s: &Vec<char>) -> (result: Vec<(char, usize)>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].1 > 0,
        forall|i: int| 0 <= i < result.len() ==> i + 1 < result.len() ==> #[trigger] result[i].0 != result[i + 1].0,
        decode_rle(result) == s@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by removing duplicate decode_rle */
    let mut result: Vec<(char, usize)> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < s.len()
        invariant
            result.len() >= 0,
            0 <= idx <= s.len(),
            decode_rle(result) == s@.subrange(0, idx as int),
            result.len() == 0 || result[result.len() - 1].1 > 0,
            forall|i: int| 0 <= i < result.len() as int ==> i + 1 < result.len() as int ==> result[i as usize].0 != result[(i + 1) as usize].0,
        decreases s.len() - idx,
    {
        let mut count: usize = 1;
        let current_char = s[idx];
        let mut next_idx = idx + 1;
        
        while next_idx < s.len() && s[next_idx] == current_char
            invariant
                next_idx > idx,
                count == next_idx - idx,
                next_idx <= s.len(),
            decreases s.len() - next_idx,
        {
            count = count + 1;
            next_idx = next_idx + 1;
        }
        
        result.push((current_char, count));
        proof {
            lemma_seq_index_len(s@, idx as int);
        }
        idx = next_idx;
    }
    
    result
}
// </vc-code>

}
fn main() {}