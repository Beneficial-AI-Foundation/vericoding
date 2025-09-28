// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec
/* helper modified by LLM (iteration 4): Minor update to comment for iteration tracking. */
fn split_one(s: Seq<char>, sep: Seq<char>) -> (result: (Seq<char>, Seq<char>, Seq<char>))
    ensures
        result.0 + result.1 + result.2 == s,
        result.1 == sep || result.1.len() == 0,
        result.1.len() == 0 ==> result.2.len() == 0 && result.0 == s,
        s.len() == result.0.len() + result.1.len() + result.2.len()
{
    let mut idx: int = 0;
    while idx <= (s.len() as int) - (sep.len() as int)
        invariant
            0 <= idx <= (s.len() as int) - (sep.len() as int) + 1,
            forall |j: int| 0 <= j < idx ==> !(s.subrange(j as usize, (j + (sep.len() as int)) as usize) == sep),
        decreases (s.len() as int) - idx
    {
        if s.subrange(idx as usize, (idx + (sep.len() as int)) as usize) == sep {
            return (s.subrange(0, idx as usize), sep, s.subrange((idx + (sep.len() as int)) as usize, s.len() as usize));
        }
        idx = idx + 1;
    }
    return (s, Seq::empty(), Seq::empty());
}
// </vc-helpers>

// <vc-spec>
fn partition(a: Vec<String>, sep: String) -> (result: (Vec<String>, Vec<String>, Vec<String>))
    ensures
        result.0.len() == a.len() && result.1.len() == a.len() && result.2.len() == a.len(),
        forall|i: int| 0 <= i < a.len() as int ==> {
            let original = #[trigger] a[i]@;
            let before_i = result.0[i]@;
            let sep_i = result.1[i]@;
            let after_i = result.2[i]@;

            before_i + sep_i + after_i == original &&

            (sep_i == sep@ || sep_i.len() == 0) &&

            (sep_i.len() == 0 ==> after_i.len() == 0 && before_i == original) &&

            original.len() == before_i.len() + sep_i.len() + after_i.len()
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed String creation using String::from_chars instead of vstd::string::from_chars to resolve compilation error. */
{
    let mut before: Vec<String> = Vec::new();
    let mut sep_vec: Vec<String> = Vec::new();
    let mut after: Vec<String> = Vec::new();
    let a_spec = a@;
    let sep_spec = sep@;
    let mut i: usize = 0;
    while i < a_spec.len()
        invariant
            0 <= (i as int) <= (a_spec.len() as int),
            (before@.len() as int) == (i as int) &&
            (sep_vec@.len() as int) == (i as int) &&
            (after@.len() as int) == (i as int),
        decreases (a_spec.len() as int) - (i as int)
    {
        let split = split_one(a_spec@[i], sep_spec);
        before.push(String::from_chars(split.0));
        sep_vec.push(String::from_chars(split.1));
        after.push(String::from_chars(split.2));
        i = i + 1;
    }
    return (before, sep_vec, after);
}
// </vc-code>

}
fn main() {}