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

proof fn lemma_substring_contains<T>(seq: Seq
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

proof fn lemma_substring_contains<T>(seq: Seq
// </vc-code>

fn main() {}
}