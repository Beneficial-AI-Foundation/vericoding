// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-preamble>

// <vc-helpers>
spec fn is_titlecased(s: Seq<char>) -> bool {
    s.len() > 0 &&
    'A' <= s[0] && s[0] <= 'Z' &&
    forall|i: int| 1 <= i < s.len() ==> ('a' <= s[i] && s[i] <= 'z')
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
    let mut result = Vec::new();
    let mut i: int = 0;
    while i < a.len()
        invariant
            a@ == old(a)@,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == is_titlecased(a[k]@),
        decreases a.len() - i
    {
        let s = &a[i];
        let s_view = s@;
        let mut current_is_titlecased = false;
        if s_view.len() > 0 {
            let first_char = s_view.index(0);
            if 'A' <= first_char && first_char <= 'Z' {
                let mut rest_are_lowercase = true;
                let mut j: int = 1;
                while j < s_view.len()
                    invariant
                        1 <= j <= s_view.len(),
                        s@ == old(s)@,
                        rest_are_lowercase == forall|k: int| 1 <= k < j ==> ('a' <= s_view[k] && s_view[k] <= 'z'),
                    decreases s_view.len() - j
                {
                    let c = s_view.index(j);
                    if !('a' <= c && c <= 'z') {
                        rest_are_lowercase = false;
                        break;
                    }
                    j = j + 1;
                }
                if rest_are_lowercase {
                    current_is_titlecased = true;
                }
            }
        }
        result.push(current_is_titlecased);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}