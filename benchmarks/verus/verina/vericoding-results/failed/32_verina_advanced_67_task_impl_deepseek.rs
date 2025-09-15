// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Remove duplicate decode_rle definition and fix helper functions */
spec fn all_pairs_bounded(pairs: Vec<(char, usize)>) -> bool {
    forall|i: int| 0 <= i < pairs.len() ==> pairs[i].1 > 0
}
spec fn adjacent_pairs_distinct(pairs: Vec<(char, usize)>) -> bool {
    forall|i: int| 0 <= i < pairs.len() - 1 ==> pairs[i].0 != pairs[i + 1].0
}
spec fn total_length(pairs: Vec<(char, usize)>) -> u64 {
    let mut sum: u64 = 0;
    let mut idx: int = 0;
    while idx < pairs.len() {
        sum = sum + (pairs[idx].1 as u64);
        idx = idx + 1;
    };
    sum
}
spec fn matches_original(s: Seq<char>, pairs: Vec<(char, usize)>) -> bool {
    if pairs.len() == 0 {
        return s.len() == 0;
    }
    let mut seq: Seq<char> = Seq::empty();
    let mut idx: int = 0;
    while idx < pairs.len() {
        let ch = pairs[idx].0;
        let cnt = pairs[idx].1 as nat;
        seq = seq + Seq::new(cnt, |i| ch);
        idx = idx + 1;
    };
    seq == s
}
spec fn is_valid_rle(s: Seq<char>, pairs: Vec<(char, usize)>) -> bool {
    all_pairs_bounded(pairs) &&
    adjacent_pairs_distinct(pairs) &&
    matches_original(s, pairs) &&
    total_length(pairs) == s.len() as u64
}
proof fn lemma_rle_properties_maintained(s: Seq<char>, pairs: Vec<(char, usize)>)
    requires is_valid_rle(s, pairs)
    ensures 
        forall|i: int| 0 <= i < pairs.len() ==> #[trigger] pairs[i].1 > 0,
        forall|i: int| 0 <= i < pairs.len() - 1 ==> #[trigger] pairs[i].0 != pairs[i + 1].0,
        decode_rle(pairs) == s
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
/* code modified by LLM (iteration 5): Remove proof call that causes circular dependency */
{
    let mut result: Vec<(char, usize)> = Vec::new();
    let mut i: usize = 0;
    let n: usize = s.len();
    
    while i < n {
        let current_char: char = s[i];
        let mut count: usize = 1;
        
        while i + count < n && s[i + count] == current_char {
            count = count + 1;
        }
        
        result.push((current_char, count));
        i = i + count;
    }
    
    result
}
// </vc-code>

}
fn main() {}