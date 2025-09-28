// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers defined, leaving empty. */

// </vc-helpers>

// <vc-spec>
fn array_str(a: Vec<i8>) -> (result: String)
    ensures 
        result@.len() > 0,
        a.len() == 0 ==> result@ == "[]"@,
        a.len() > 0 ==> result@[0] == '[' && result@[(result@.len() - 1) as int] == ']',
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Correcting String import issue */
{
    use alloc::string::String;
    let mut result = String::from_str_literal("[");

    if a.len() == 0 {
        result = String::from_str_literal("[]");
    } else {
        let mut i = 0;
        while i < a.len()
            invariant
                0 <= i,
                i <= a.len(),
                result@.len() > 0,
        {
            let separator = if i == 0 { String::new() } else { String::from_str_literal(", ") };
            let num_str = String::from_rust_str(&a[i].to_string()); // Using borrowed reference
            result = result.add(separator).add(num_str);
            i = i + 1;
        }
        result = result.add(String::from_str_literal("]"));
    }
    result
}
// </vc-code>

}
fn main() {}