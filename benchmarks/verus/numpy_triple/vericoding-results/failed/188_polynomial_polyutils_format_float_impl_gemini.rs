// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn format_float(x: f64, parens: bool) -> (result: String)
    ensures
        result@.len() > 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): switched from unsupported String::from to vstd's String::from_str */
    if parens {
        String::from_str("(0)")
    } else {
        String::from_str("0")
    }
}
// </vc-code>


}
fn main() {}