// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): convert Seq<char> to Vec<char> */
fn vec_from_seq_char(s: Seq<char>) -> (result: Vec<char>)
    ensures
        result.len() == s.len(),
        forall|i: nat| i < result.len() ==> result[i]@ == s@[i],
{
    let mut result: Vec<char> = Vec::new();
    let mut i: nat = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            result.len() == i,
        decreases s.len() - i
    {
        result.push(s@[i]);
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
spec fn char_to_lower(c: char) -> char;

spec fn string_to_lower(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        seq![char_to_lower(s[0])] + string_to_lower(s.skip(1))
    }
}

fn lower(a: Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@ == string_to_lower(a[i]@),
        forall|i: int| 0 <= i < a.len() ==> result[i].len() == a[i].len(),
        forall|i: int| 0 <= i < a.len() ==> (a[i].len() == 0 ==> result[i].len() == 0),
        forall|i: int| 0 <= i < a.len() ==> string_to_lower(result[i]@) == result[i]@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): build result by converting inner sequences using string_to_lower and vec_from_seq_char */
    let mut result: Vec<Vec<char>> = Vec::new();

    let mut i: nat = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
        decreases a.len() - i
    {
        let inner_seq: Seq<char> = string_to_lower(a[i]@);
        let v: Vec<char> = vec_from_seq_char(inner_seq);
        result.push(v);
        i = i + 1;
    }

    result
}
// </vc-code>


}
fn main() {}