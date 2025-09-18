// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified character extraction using char */
proof fn lemma_join_chars_len(separator: Seq<char>, chars: Seq<char>)
    requires chars.len() > 1
    ensures join_chars(separator, chars).len() == chars.len() + (chars.len() - 1) * separator.len()
    decreases chars.len()
{
    if chars.len() == 2 {
        assert(join_chars(separator, chars) == chars.take(1) + separator + chars.skip(1));
        assert(chars.skip(1).len() == 1);
        assert(join_chars(separator, chars.skip(1)) == chars.skip(1));
    } else {
        lemma_join_chars_len(separator, chars.skip(1));
    }
}

proof fn lemma_join_chars_base_cases(separator: Seq<char>, chars: Seq<char>)
    ensures chars.len() == 0 ==> join_chars(separator, chars).len() == 0,
            chars.len() == 1 ==> join_chars(separator, chars) == chars
{
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
    /* code modified by LLM (iteration 5): fixed nat literal syntax error */
    let mut result: Vec<String> = Vec::new();
    
    for i in 0..seq.len()
        invariant
            result.len() == i,
            sep.len() == seq.len(),
            forall|j: int| #![trigger result[j]] 0 <= j < i ==> {
                let s = seq[j]@;
                let separator = sep[j]@;
                (s.len() <= 1 ==> result[j]@ == s) &&
                (s.len() > 1 ==> result[j]@ == join_chars(separator, s)) &&
                (s.len() > 1 ==> result[j]@.len() == s.len() + (s.len() - 1) * separator.len()) &&
                (s.len() == 0 ==> result[j]@.len() == 0) &&
                (s.len() == 1 ==> result[j]@ == s) &&
                (s.len() > 0 ==> result[j]@.len() > 0)
            }
    {
        let chars = &seq[i];
        let separator = &sep[i];
        
        if chars@.len() <= 1 {
            result.push(chars.clone());
        } else {
            proof {
                lemma_join_chars_len(separator@, chars@);
                lemma_join_chars_base_cases(separator@, chars@);
            }
            
            let mut joined = String::new();
            for j in 0..chars.len()
                invariant
                    j <= chars.len(),
                    chars@.len() > 1,
                    j == 0 ==> joined@ == Seq::<char>::empty(),
                    j > 0 ==> joined@.len() == j + (j - 1) * separator@.len()
            {
                if j > 0 {
                    joined.push_str(separator);
                }
                joined.push(chars.as_bytes()[j] as char);
            }
            result.push(joined);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}