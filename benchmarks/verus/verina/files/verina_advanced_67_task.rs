use vstd::prelude::*;

verus! {

spec fn decode_rle(lst: Vec<(char, usize)>) -> Seq<char> {
    Seq::empty()
}

fn run_length_encode(s: &Vec<char>) -> (result: Vec<(char, usize)>)
    ensures
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].1 > 0,
        forall|i: int| 0 <= i < result.len() ==> i + 1 < result.len() ==> #[trigger] result[i].0 != result[i + 1].0,
        decode_rle(result) == s@,
{
    assume(false);
    unreached()
}

}
fn main() {}