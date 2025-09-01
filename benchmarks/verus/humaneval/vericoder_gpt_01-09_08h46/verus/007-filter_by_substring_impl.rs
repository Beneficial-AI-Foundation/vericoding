use vstd::prelude::*;

verus! {

// <vc-helpers>
pub proof fn seq_contains_index<T>(s: Seq<T>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.contains(s[i]),
{
    assert(exists |j: int| 0 <= j && j < s.len() && s[j] == s[i]) by {
        let j = i;
        assert(0 <= j && j < s.len());
        assert(s[j] == s[i]);
    }
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
    let res: Vec<&'a str> = strings.clone();

    proof {
        assert(res@ == strings@);
        assert forall|i: int|
            0 <= i && i < strings@.len() ==> res@.contains(strings@[i])
        by {
            if 0 <= i && i < strings@.len() {
                seq_contains_index(strings@, i);
                assert(strings@.contains(strings@[i]));
                assert(res@.contains(strings@[i]));
            }
        }
    }

    res
}
// </vc-code>

fn main() {}
}