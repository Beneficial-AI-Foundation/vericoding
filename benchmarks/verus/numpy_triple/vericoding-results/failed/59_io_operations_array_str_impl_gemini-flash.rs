// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn helper_f32_to_str(f: f32) -> (s: String) { vstd::string::f32_to_string(f) }
// </vc-helpers>

// <vc-spec>
fn array_str(a: Vec<f32>) -> (result: String)
    ensures 
        result@.len() > 0,
        a.len() == 0 ==> result@ == "[]"@,
        a.len() > 0 ==> result@[0] == '[' && result@[(result@.len() - 1) as int] == ']',
// </vc-spec>
// <vc-code>
{
    let mut result_str = String::from("[");
    if a.len() > 0 {
        let mut first = true;
        let mut i = 0;
        while i < a.len()
            invariant 0 <= i,
            invariant i <= a.len(),
            invariant first == (i == 0),
            invariant {
                (forall |j: int| 0 <= j < i ==> 
                    exists |k: int| 0 <= k < result_str@.len() && 
                    result_str@.subsequence(k, k + helper_f32_to_str(a[j]).len()) == helper_f32_to_str(a[j])@ &&
                    (if j == 0 { result_str@.subsequence(1, 1 + helper_f32_to_str(a[0]).len()) == helper_f32_to_str(a[0])@ } else { 
                        true // Simplified for now to fix compile error
                    }))
            }
        {
            if !first {
                result_str.push_str(", ");
            }
            let f_str = helper_f32_to_str(a[i]);
            result_str.push_str(&f_str);
            first = false;
            i = i + 1;
        }
    }
    result_str.push(']');
    result_str
}
// </vc-code>

}
fn main() {}