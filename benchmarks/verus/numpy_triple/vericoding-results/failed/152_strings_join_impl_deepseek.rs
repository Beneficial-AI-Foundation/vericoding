// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate spec function and fixed lemma syntax */
proof fn lemma_join_chars_len(separator: Seq<char>, chars: Seq<char>)
    ensures
        join_chars(separator, chars).len() == if chars.len() <= 1 {
            chars.len()
        } else {
            chars.len() + (chars.len() - 1) * separator.len()
        }
    decreases chars.len()
{
    if chars.len() > 1 {
        lemma_join_chars_len(separator, chars.skip(1));
    }
}

spec fn string_to_chars(s: Seq<char>) -> Seq<char> {
    s
}

spec fn chars_to_string_len(chars: Seq<char>) -> nat {
    chars.len()
}
// </vc-helpers>

// <vc-spec>
spec fn join_chars(separator: Seq<char>, chars: Seq<char>) -> Seq<char>
    decreases chars.len()
{
    if chars.len() <= 1 {
        chars
    } else {
        chars.take(1) + separator + join_chars(separator, chars.skip(1))
    }
}

spec fn string_to_chars(s: Seq<char>) -> Seq<char> {
    s
}

spec fn chars_to_string_len(chars: Seq<char>) -> nat {
    chars.len()
}

fn join(sep: Vec<String>, seq: Vec<String>) -> (result: Vec<String>)
    requires sep.len() == seq.len(),
    ensures
        result.len() == sep.len(),
        forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> {
            let s = seq[i]@;
            let separator = sep[i]@;

            (s.len() <= 1 ==> result[i]@ == s) &&
            (s.len() > 1 ==> result[i]@ == join_chars(separator, s)) &&

            (s.len() > 1 ==> result[i]@.len() == s.len() + (s.len() - 1) * separator.len()) &&

            (s.len() == 0 ==> result[i]@.len() == 0) &&

            (s.len() == 1 ==> result[i]@ == s) &&

            (s.len() > 0 ==> result[i]@.len() > 0)
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed ensures syntax placement */
{
    let mut result = Vec::new();
    let n = sep.len();
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> {
                let s = seq[j]@;
                let separator = sep[j]@;
                result[j]@ == join_chars(separator, s),
                result[j]@.len() == if s.len() <= 1 { s.len() } else { s.len() + (s.len() - 1) * separator.len() }
            }
    {
        let s_chars = seq[i]@;
        let separator_chars = sep[i]@;
        let joined_chars = join_chars(separator_chars, s_chars);
        result.push(String::from_str(joined_chars));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}