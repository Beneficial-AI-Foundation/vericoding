// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): runtime recursive join matching join_chars */
fn join_into(separator: String, s: String) -> (res: String) ensures res@ == join_chars(separator@, s@) decreases s@.len() {
    if s.chars().count() <= 1 {
        let r = s;
        proof {
            assert(r@ == s@);
            assert(join_chars(separator@, s@) == s@);
            assert(r@ == join_chars(separator@, s@));
        }
        r
    } else {
        let mut iter = s.chars();
        let first = iter.next().unwrap();
        let rest_s: String = iter.collect();
        let rest_res = join_into(separator.clone(), rest_s.clone());
        let mut r = String::new();
        r.push(first);
        r.push_str(&separator);
        r.push_str(&rest_res);
        proof {
            assert(rest_s@ == s@.skip(1));
            assert(rest_res@ == join_chars(separator@, rest_s@));
            assert(r@ == s@.take(1) + separator@ + rest_res@);
            assert(r@ == join_chars(separator@, s@));
        }
        r
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
    /* code modified by LLM (iteration 5): build result with invariant and use join_into; fix index types */
    let mut result: Vec<String> = Vec::new();
    let mut i: int = 0;
    while i < sep.len()
        invariant i <= sep.len(),
        invariant result.len() == i,
        invariant forall|k: int| 0 <= k && k < i ==> {
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
        let r = join_into(sep[i].clone(), seq[i].clone());
        result.push(r);
        proof {
            let s = seq[i]@;
            let separator = sep[i]@;
            assert((s.len() <= 1 ==> result[i]@ == s) &&
                   (s.len() > 1 ==> result[i]@ == join_chars(separator, s)));
            assert((s.len() > 1 ==> result[i]@.len() == s.len() + (s.len() - 1) * separator.len()));
            assert((s.len() == 0 ==> result[i]@.len() == 0));
            assert((s.len() == 1 ==> result[i]@ == s));
            assert((s.len() > 0 ==> result[i]@.len() > 0));
        }
        i += 1;
    }
    result
}

// </vc-code>

}
fn main() {}