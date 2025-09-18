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
    /* code modified by LLM (iteration 5): Fix nat literal syntax error */
    let mut result: Vec<String> = Vec::new();
    let n = sep.len();
    
    for i in 0..n
        invariant
            result.len() == i,
            sep.len() == n,
            seq.len() == n,
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
        let s = &seq[i];
        let separator = &sep[i];
        
        if s@.len() <= 1 {
            result.push(s.clone());
        } else {
            let mut joined = String::new();
            proof {
                let first_char = s@.take(1int);
            }
            let first_str = String::from_utf8(vec![s.as_bytes()[0]]).unwrap();
            joined.push_str(&first_str);
            
            let len = s.len();
            for j in 1..len
                invariant
                    1 <= j <= len,
                    j <= s@.len(),
                    joined@.len() == j + (j - 1) * separator@.len(),
                    joined@ == join_chars(separator@, s@.take(j as int))
            {
                joined.push_str(separator);
                proof {
                    let char_at_j = s@.subrange(j as int, (j + 1) as int);
                }
                let char_str = String::from_utf8(vec![s.as_bytes()[j]]).unwrap();
                joined.push_str(&char_str);
            }
            
            result.push(joined);
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}