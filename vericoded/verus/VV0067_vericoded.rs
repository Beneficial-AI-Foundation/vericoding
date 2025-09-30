// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn helper_noop() { }
// </vc-helpers>

// <vc-spec>
spec fn is_digit(c: char) -> bool {
    '0' <= c && c <= '9'  
}

proof fn run_length_encoder_property(input: String, result: String)
    requires

        input@ == Seq::<char>::empty() <==> result@ == Seq::<char>::empty(),

        (result@.len() > 0 ==> (
            forall|i: int| 0 <= i < result@.len() ==> 
                (i % 2 == 0 ==> !is_digit(result@[i])) &&
                (i % 2 == 1 ==> is_digit(result@[i]))
        )),
// </vc-spec>
// <vc-code>
{
}

// </vc-code>

}
fn main() {}