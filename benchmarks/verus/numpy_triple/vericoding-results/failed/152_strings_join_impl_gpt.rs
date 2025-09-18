// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): length lemma for join_chars establishing exact size */
proof fn lemma_join_len(separator: Seq<char>, chars: Seq<char>)
    ensures
        chars.len() <= 1 ==> join_chars(separator, chars).len() == chars.len(),
        chars.len() > 1 ==> join_chars(separator, chars).len() ==
            chars.len() + (chars.len() - 1) * separator.len()
    decreases chars.len()
{
    if chars.len() <= 1 {
    } else {
        lemma_join_len(separator, chars.skip(1));
        assert(chars.take(1).len() == 1);
        assert(chars.skip(1).len() == chars.len() - 1);
        let j = join_chars(separator, chars);
        assert(j == chars.take(1) + separator + join_chars(separator, chars.skip(1)));
        let rest_len = join_chars(separator, chars.skip(1)).len();
        if chars.skip(1).len() <= 1 {
            assert(rest_len == chars.skip(1).len());
            assert(j.len() == (chars.take(1) + separator + join_chars(separator, chars.skip(1))).len());
            assert(j.len() == 1 + separator.len() + rest_len);
            assert(j.len() == 1 + separator.len() + chars.skip(1).len());
            assert(chars.skip(1).len() == chars.len() - 1);
            assert(j.len() == chars.len() + (chars.len() - 1) * separator.len());
        } else {
            assert(rest_len == chars.skip(1).len() + (chars.skip(1).len() - 1) * separator.len());
            assert(j.len() == (chars.take(1) + separator + join_chars(separator, chars.skip(1))).len());
            assert(j.len() == 1 + separator.len() + rest_len);
            assert(j.len() == 1 + separator.len() + chars.skip(1).len() + (chars.skip(1).len() - 1) * separator.len());
            assert(chars.skip(1).len() == chars.len() - 1);
            assert(j.len() == 1 + separator.len() + (chars.len() - 1) + (chars.len() - 2) * separator.len());
            assert(j.len() == chars.len() + (chars.len() - 1) * separator.len());
        }
    }
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
{
    /* code modified by LLM (iteration 5): construct each output string via std::string::String::from_chars and maintain loop invariant */
    let n: usize = sep.len();
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            sep.len() == n,
            seq.len() == n,
            result.len() == i,
            0 <= i as int <= n as int,
            forall|j: int| #![trigger result[j]] 0 <= j < result.len() as int ==> result[j]@ == join_chars(sep[j]@, seq[j]@)
        decreases n as int - i as int
    {
        let out_i = std::string::String::from_chars(join_chars(sep[i]@, seq[i]@));
        result.push(out_i);
        i = i + 1;
    }
    assert(result.len() == n);
    assert(result.len() == sep.len());
    assert forall|k: int| #![trigger result[k]] 0 <= k < result.len() as int ==> {
        let s = seq[k]@;
        let separator = sep[k]@;

        (s.len() <= 1 ==> result[k]@ == s) &&
        (s.len() > 1 ==> result[k]@ == join_chars(separator, s)) &&

        (s.len() > 1 ==> result[k]@.len() == s.len() + (s.len() - 1) * separator.len()) &&

        (s.len() == 0 ==> result[k]@.len() == 0) &&

        (s.len() == 1 ==> result[k]@ == s) &&

        (s.len() > 0 ==> result[k]@.len() > 0)
    } by {
        let s = seq[k]@;
        let separator = sep[k]@;
        assert(result[k]@ == join_chars(separator, s));
        proof { lemma_join_len(separator, s); }
        if s.len() <= 1 {
            assert(join_chars(separator, s) == s);
            assert(result[k]@ == s);
            assert(result[k]@.len() == s.len());
            if s.len() == 0 {
                assert(result[k]@.len() == 0);
            }
            if s.len() == 1 {
                assert(result[k]@ == s);
            }
        } else {
            assert(result[k]@.len() == s.len() + (s.len() - 1) * separator.len());
            assert(s.len() > 0);
            assert(result[k]@.len() > 0);
        }
        if s.len() > 0 && s.len() <= 1 {
            assert(result[k]@ == s);
            assert(result[k]@.len() > 0);
        }
    };
    result
}
// </vc-code>

}
fn main() {}