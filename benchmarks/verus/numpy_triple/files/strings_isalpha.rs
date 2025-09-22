// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool {
    ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z')
}

spec fn all_chars_alpha(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_alpha_char(s[0]) && all_chars_alpha(s.skip(1))
    }
}

fn isalpha(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i as int] == (a[i as int]@.len() > 0 && all_chars_alpha(a[i as int]@)),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() == 0 ==> result[i as int] == false),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i as int]@.len() > 0 ==> (result[i as int] <==> all_chars_alpha(a[i as int]@))),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> a[i as int]@.len() > 0),
        forall|i: int| 0 <= i < a.len() ==> 
            (result[i as int] == true ==> all_chars_alpha(a[i as int]@))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}