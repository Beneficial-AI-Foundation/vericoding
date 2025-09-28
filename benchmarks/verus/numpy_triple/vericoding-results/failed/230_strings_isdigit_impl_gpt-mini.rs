// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for digit characters */
spec fn is_digit_char(c: char) -> bool { c >= '0' && c <= '9' }

/* helper modified by LLM (iteration 5): predicate that all chars in a sequence are digits */
spec fn all_chars_digit(s: Seq<char>) -> bool { forall|i: nat| i < s.len() ==> is_digit_char(s[i]) }
// </vc-helpers>

// <vc-spec>
spec fn all_chars_digit(s: Seq<char>) -> bool;

fn isdigit(a: Vec<String>) -> (result: Vec<bool>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i as int] == (a[i as int]@.len() > 0 && all_chars_digit(a[i as int]@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate strings and check non-empty + all digits using nat indices */
    let n: usize = a.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
        decreases (n as int - i as int)
    {
        let s_seq: Seq<char> = a[i]@;
        let mut ok: bool = true;
        if s_seq.len() == 0 {
            ok = false;
        } else {
            let m: nat = s_seq.len();
            let mut j: nat = 0;
            while j < m
                invariant
                    j <= m,
                    ok ==> forall|k: nat| k < j ==> is_digit_char(s_seq[k]),
                decreases (m - j)
            {
                let c: char = s_seq[j];
                if !is_digit_char(c) {
                    ok = false;
                    j = m;
                } else {
                    j = j + 1;
                }
            }
        }
        result.push(ok);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}