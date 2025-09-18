// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): removed type annotation from for loop to fix compilation */
    let mut result: Vec<String> = Vec<String>::new();
    assert(seq.len() == sep.len());
    for i in 0..seq.len()
        invariant
            result.len() == i,
            forall |k: usize| #![trigger result[k]] 0 <= k < i ==> {
                let s = seq[k]@;
                let separator = sep[k]@;
                (s.len() <= 1 ==> result[k]@ == s) &&
                (s.len() > 1 ==> result[k]@ == join_chars(separator, s)) &&
                (s.len() > 1 ==> result[k]@.len() == s.len() + (s.len() - 1) * separator.len()) &&
                (s.len() == 0 ==> result[k]@.len() == 0) &&
                (s.len() == 1 ==> result[k]@ == s) &&
                (s.len() > 0 ==> result[k]@.len() > 0)
            }
    {
        let s = seq[i]@;
        let separator = sep[i]@;
        let s_len = s.len();
        if s_len <= 1 {
            result.push(s.to_vec());
            if s_len == 0 {
                assert(result[i]@.len() == 0);
            }
            if s_len == 1 {
                assert(result[i]@ == s);
            }
        } else {
            let mut joined: Seq<char> = Seq::empty();
            for j in 0..s_len {
                if j > 0 {
                    for k in 0..separator.len() {
                        joined = joined.append(Seq::new_1(separator[k]));
                    }
                }
                joined = joined.append(Seq::new_1(s[j]));
            }
            result.push(joined.to_vec());
            assert(result[i]@ == join_chars(separator, s));
            assert(result[i]@.len() == s.len() + (s.len() - 1) * separator.len());
            assert(result[i]@.len() > 0);
        }
    }
    result
}
// </vc-code>

}
fn main() {}