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
        forall|i: int| 0 <= i < result.len() ==> {
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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}