// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn contains_index_char(s: Seq<char>, i: int)
    requires
        0 <= i < s.len()
    ensures
        s.contains(s[i])
{ }
// </vc-helpers>

// <vc-spec>
fn remove_chars(str1: &Vec<char>, str2: &Vec<char>) -> (result: Vec<char>)

    ensures
        forall|i: int|
            0 <= i < result.len() ==> (str1@.contains(#[trigger] result[i]) && !str2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < str1.len() ==> (str2@.contains(#[trigger] str1[i]) || result@.contains(
                #[trigger] str1[i],
            )),
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < str1.len()
        invariant
            i <= str1.len(),
            forall|k: int|
                0 <= k < result.len() ==> (str1@.contains(#[trigger] result[k]) && !str2@.contains(#[trigger] result[k])),
            forall|k: int|
                0 <= k < i as int ==> (str2@.contains(#[trigger] str1[k]) || result@.contains(#[trigger] str1[k])),
        decreases str1.len() - i
    {
        let c = str1[i];
        if !str2@.contains(c) {
            proof {
                contains_index_char(str1@, i as int);
            }
            let old_len = result.len();
            result.push(c);
            proof {
                contains_index_char(result@, old_len as int);
                assert(result@[old_len as int] == c);
                assert(result@.contains(c));
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}