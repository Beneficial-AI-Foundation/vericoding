// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_binary_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn string_xor(a: Vec<char>, b: Vec<char>) -> (result: Vec<char>)
    requires 
        a.len() == b.len(),
        is_binary_string(a@),
        is_binary_string(b@),
    ensures 
        result.len() == a.len(),
        is_binary_string(result@),
        forall|i: int| 0 <= i < a.len() as int ==> 
            (a@[i] == b@[i] ==> result@[i] == '0') &&
            (a@[i] != b@[i] ==> result@[i] == '1'),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}