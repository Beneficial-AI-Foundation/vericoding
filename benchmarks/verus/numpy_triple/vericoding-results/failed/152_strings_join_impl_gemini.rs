// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added string_to_vec_char helper and improved proofs */
fn string_to_vec_char(s: &String) -> (res: Vec<char>)
    ensures res@ == s@,
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            res@ == s@.take(i as nat),
            i <= s.len(),
    {
        res.push(s.get_char(i as nat));
        i = i + 1;
    }
    res
}

proof fn lemma_join_chars_len(separator: Seq<char>, chars: Seq<char>)
    requires
        chars.len() > 1,
    ensures
        join_chars(separator, chars).len() == chars.len() + (chars.len() - 1) * separator.len(),
    decreases chars.len(),
{
    let rest = chars.skip(1);
    assert(join_chars(separator, chars) == chars.take(1) + separator + join_chars(separator, rest));
    if rest.len() > 1 {
        lemma_join_chars_len(separator, rest);
        assert(join_chars(separator, rest).len() == rest.len() + (rest.len() - 1) * separator.len());
    } else {
        assert(join_chars(separator, rest) == rest);
    }
}

fn join_one_string(separator: &Vec<char>, chars: &Vec<char>) -> (result: Vec<char>)
    ensures
        result@ == join_chars(separator@, chars@),
    decreases chars.len(),
{
    if chars.len() <= 1 {
        chars.clone()
    } else {
        let mut first = Vec::new();
        first.push(chars[0]);

        let mut rest_vec = chars.clone();
        rest_vec.remove(0);

        let mut joined_rest = join_one_string(separator, &rest_vec);

        let mut res = first;
        res.append(&mut separator.clone());
        res.append(&mut joined_rest);

        proof {
            assert(first@ == chars@.take(1));
            assert(rest_vec@ == chars@.skip(1));
            assert(joined_rest@ == join_chars(separator@, rest_vec@));
            assert(res@ == first@ + separator@ + joined_rest@);
            assert(res@ == chars@.take(1) + separator@ + join_chars(separator@, chars@.skip(1)));
            assert(res@ == join_chars(separator@, chars@));
        }
        res
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
/* code modified by LLM (iteration 5): Replaced non-existent string functions with correct helpers */
{
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < seq.len()
        invariant
            0 <= i <= seq.len(),
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
            },
        decreases seq.len() - i,
    {
        let s = &seq[i];
        let separator = &sep[i];

        let s_vec = string_to_vec_char(s);
        let separator_vec = string_to_vec_char(separator);

        let joined_chars_vec = join_one_string(&separator_vec, &s_vec);

        proof {
            assert(s_vec@ == s@);
            assert(separator_vec@ == separator@);
            assert(joined_chars_vec@ == join_chars(separator@, s@));
            if s@.len() > 1 {
                lemma_join_chars_len(separator@, s@);
                assert(joined_chars_vec@.len() == join_chars(separator@, s@).len());
            }
        }
        
        let new_string = vstd::string::vec_to_string(&joined_chars_vec);
        
        proof {
            assert(new_string@ == joined_chars_vec@);
        }

        result.push(new_string);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}