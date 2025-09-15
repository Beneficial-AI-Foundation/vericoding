// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}
// </vc-preamble>

// <vc-helpers>
spec fn decode_rle_helper(lst: Vec<(char, usize)>, index: usize) -> Seq<char>
    decreases lst.len() - index
{
    if index >= lst.len() {
        Seq::empty()
    } else {
        let (ch, count) = lst[index];
        Seq::new(count, |_: int| ch) + decode_rle_helper(lst, index + 1)
    }
}

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    decode_rle_helper(lst, 0)
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
    let mut result: Vec<(char, usize)> = Vec::new();
    
    if s.len() == 0 {
        return result;
    }
    
    let mut current_char = s[0];
    let mut count: usize = 1;
    
    let mut i = 1;
    while i < s.len() {
        if s[i] == current_char {
            count += 1;
        } else {
            result.push((current_char, count));
            current_char = s[i];
            count = 1;
        }
        i += 1;
    }
    
    result.push((current_char, count));
    result
}
// </vc-code>

}
fn main() {}