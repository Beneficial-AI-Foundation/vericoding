// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-preamble>

// <vc-helpers>
spec fn is_titlecased(s: Seq<char>) -> bool {
    if s.len() == 0 {
        false
    } else {
        s[0].is_ascii_uppercase()
        && forall |i: int| 1 <= i < s.len() ==> s[i].is_ascii_lowercase()
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
    let mut result: Vec<bool> = Vec::new();
    let mut i: int = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall |k: int| 0 <= k < i ==> result[k] == is_titlecased(a[k]@),
    {
        let s_seq = a[i]@;
        let mut is_t = false;
        if s_seq.len() > 0 {
            is_t = s_seq[0].is_ascii_uppercase();
            if is_t {
                let mut j: int = 1;
                while j < s_seq.len()
                    invariant j <= s_seq.len(),
                {
                    if !s_seq[j].is_ascii_lowercase() {
                        is_t = false;
                    }
                    j += 1;
                }
            }
        }
        result.push(is_t);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}