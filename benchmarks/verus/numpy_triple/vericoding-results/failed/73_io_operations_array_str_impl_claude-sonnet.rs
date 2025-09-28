// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn array_str(a: Vec<i8>) -> (result: String)
    ensures 
        result@.len() > 0,
        a.len() == 0 ==> result@ == "[]"@,
        a.len() > 0 ==> result@[0] == '[' && result@[(result@.len() - 1) as int] == ']',
// </vc-spec>
// <vc-code>
{
    if a.len() == 0 {
        "[]".to_string()
    } else {
        let mut result = "[".to_string();
        let mut i = 0;
        while i < a.len()
            invariant
                i <= a.len(),
                result@.len() > 0,
                result@[0] == '[',
        {
            if i > 0 {
                result = result + ", ";
            }
            result = result + &a[i].to_string();
            i += 1;
        }
        result = result + "]";
        result
    }
}
// </vc-code>

}
fn main() {}