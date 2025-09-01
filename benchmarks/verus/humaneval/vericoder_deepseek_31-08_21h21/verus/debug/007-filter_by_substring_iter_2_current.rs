use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_substring(s: Seq<char>, sub: Seq<char>) -> bool {
    exists|j: int| 
        0 <= j <= s.len() - sub.len() && 
        s.subrange(j, j + sub.len()) == sub
}

proof fn lemma_seq_subrange_contains(s: Seq<char>, sub: Seq<char>, j: int)
    requires
        0 <= j <= s.len() - sub.len(),
    ensures
        s.subrange(j, j + sub.len()) == sub,
{
}

proof fn lemma_vec_contains<'a>(v: Vec<&'a str>, s: &'a str)
    ensures
        v@.contains(s),
{
}

proof fn lemma_forall_contains<'a>(strings: Vec<&'a str>, substring: Seq<char>, res: Vec<&'a str>)
    requires
        forall|i: int| 
            0 <= i < strings@.len() && #[trigger] contains_substring(strings@[i]@, substring) ==> 
            res@.contains(strings@[i]),
    ensures
        forall|i: int|
            0 <= i < strings@.len() && (exists|j: int|
                0 <= j <= strings@[i]@.len() - substring.len() && strings[i]@.subrange(
                    j,
                    #[trigger] (j + substring.len()),
                ) == substring) ==> res@.contains(#[trigger] (strings[i])),
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn filter_by_substring<'a>(strings: &Vec<&'a str>, substring: &str) -> (res: Vec<&'a str>)
    // post-conditions-start
    ensures
        forall|i: int|
            0 <= i < strings@.len() && (exists|j: int|
                0 <= j <= strings@[i]@.len() - substring@.len() && strings[i]@.subrange(
                    j,
                    #[trigger] (j + substring@.len()),
                ) == substring@) ==> res@.contains(#[trigger] (strings[i])),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut res = Vec::new();
    let mut idx: usize = 0;
    let substring_seq = substring.chars();
    while idx < strings.len()
        invariant
            idx <= strings.len(),
            forall|i: int| 
                0 <= i < idx && contains_substring(strings@[i]@, substring_seq@) ==> 
                res@.contains(strings@[i]),
    {
        let s = strings[idx];
        let s_chars = s.chars();
        let sub_chars = substring.chars();
        let mut found = false;
        let mut j: usize = 0;
        while j <= s_chars.len().sub(sub_chars.len())
            invariant
                j <= s_chars.len().sub(sub_chars.len()) + 1,
                !found ==> forall|k: int| 0 <= k < j ==> 
                    !(s_chars@.subrange(k, k + sub_chars@.len()) == sub_chars@),
                found ==> s_chars@.subrange(j.sub(1), j.sub(1) + sub_chars@.len()) == sub_chars@,
        {
            if s_chars@.subrange(j, j + sub_chars@.len()) == sub_chars@ {
                found = true;
                break;
            }
            j = j + 1;
        }
        if found {
            res.push(s);
            proof {
                lemma_vec_contains(res, s);
            }
        }
        idx = idx + 1;
    }
    proof {
        lemma_forall_contains(strings, substring_seq, res);
    }
    res
}
// </vc-code>

fn main() {}
}