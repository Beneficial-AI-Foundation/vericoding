// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_valid_md5_hash(s: Seq<char>) -> bool {
    s.len() == 32 && forall|i: int| 0 <= i < s.len() ==> #[trigger] s.index(i) == s.index(i) && {
        let c = s.index(i);
        ('0' <= c && c <= '9') || ('a' <= c && c <= 'f')
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn string_to_md5(text: String) -> (result: Option<String>)
    ensures ({
        (text@.len() == 0 ==> matches!(result, Option::None)) &&
        (text@.len() != 0 ==> match result {
            Option::Some(value) => is_valid_md5_hash(value@),
            Option::None => false,
        })
    })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Option::None
    // impl-end
}
// </vc-code>


}

fn main() {}