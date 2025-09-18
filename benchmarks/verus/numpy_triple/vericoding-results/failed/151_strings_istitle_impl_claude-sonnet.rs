// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate definition */
spec fn is_titlecased(s: Seq<char>) -> bool {
    if s.len() == 0 {
        false
    } else {
        let first_char = s[0];
        let first_is_upper = first_char >= 'A' && first_char <= 'Z';
        let rest_are_lower = forall|i: int| 1 <= i < s.len() ==> {
            let c = s[i];
            (c >= 'a' && c <= 'z') || !(c >= 'A' && c <= 'Z')
        };
        first_is_upper && rest_are_lower
    }
}
// </vc-helpers>

// <vc-spec>
fn istitle(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == is_titlecased(a[i]@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplified logic to avoid complex invariants */
    let mut result = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == is_titlecased(a[j]@)
    {
        let s = a[i]@;
        let is_title = if s.len() == 0 {
            false
        } else {
            let first_char = s[0];
            let first_is_upper = first_char >= 'A' && first_char <= 'Z';
            let mut rest_ok = true;
            let mut j = 1;
            while j < s.len()
                invariant
                    1 <= j <= s.len(),
                    rest_ok ==> forall|k: int| 1 <= k < j ==> {
                        let c = s[k];
                        (c >= 'a' && c <= 'z') || !(c >= 'A' && c <= 'Z')
                    }
            {
                let c = s[j];
                if c >= 'A' && c <= 'Z' {
                    rest_ok = false;
                }
                j += 1;
            }
            first_is_upper && rest_ok
        };
        result.push(is_title);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}