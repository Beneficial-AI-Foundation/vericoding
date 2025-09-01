use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_substring_range(s: Seq<char>, start: int, len: int)
    requires
        0 <= start,
        0 <= len,
        start + len <= s.len(),
    ensures
        s.subrange(start, start + len).len() == len,
{
    assert forall|i: int| 0 <= i < start + len ==> s.subrange(start, start + len)[i] == s[start + i] by {
        if i >= len {
            assert(false);
        }
    }
}

proof fn lemma_substring_contains<T>(seq: Seq<T>, sub: Seq<T>, i: int)
    requires
        0 <= i <= seq.len() - sub.len(),
        seq.subrange(i, i + sub.len()) == sub,
    ensures
        seq.contains(sub),
{
    assert(exists|j: int| 0 <= j <= seq.len() - sub.len() && seq.subrange(j, j + sub.len()) == sub);
}
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
    let substring_seq = substring@;
    let mut i = 0;
    while i < strings.len() {
        let s = strings[i];
        let s_seq = s@;
        let mut j = 0;
        let mut found = false;
        while j <= s_seq.len() - substring_seq.len() {
            if s_seq.subrange(j, j + substring_seq.len()) == substring_seq {
                found = true;
                break;
            }
            j += 1;
        }
        if found {
            res.push(s);
        }
        i += 1;
    }
    res
}
// </vc-code>

fn main() {}
}