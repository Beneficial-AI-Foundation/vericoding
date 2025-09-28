// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_alpha_char(c: char) -> bool {
    let code = c as u32;
    (code >= 65 && code <= 90) || (code >= 97 && code <= 122)
}

spec fn is_upper_char(c: char) -> bool {
    let code = c as u32;
    code >= 65 && code <= 90
}
// </vc-helpers>

// <vc-spec>
spec fn is_alpha_char(c: char) -> bool;

spec fn is_upper_char(c: char) -> bool;

spec fn has_alpha_chars(s: Seq<char>) -> bool {
    exists|i: int| 0 <= i < s.len() && is_alpha_char(s[i])
}

spec fn all_alpha_are_upper(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() && is_alpha_char(s[i]) ==> is_upper_char(s[i])
}

fn isupper(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i] == {
            let s = a[i]@;
            s.len() > 0 && has_alpha_chars(s) && all_alpha_are_upper(s)
        }
// </vc-spec>
// <vc-code>

{
    let mut result = Vec::with_capacity(a.len() as usize);
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a@.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] result@[k] == {
                let ss = a@[k];
                ss.len() > 0 && has_alpha_chars(ss) && all_alpha_are_upper(ss)
            },
        decreases a@.len() - i
    {
        let s_bytes = a[i].as_bytes();
        let len_s = s_bytes.length();
        if len_s == 0 {
            result.push(false);
            i += 1;
            continue;
        }
        let mut found_alpha = false;
        let mut found_bad = false;
        let mut j = 0;
        while j < len_s
            invariant
                0 <= j <= len_s,
                found_alpha == (exists|jj: int| 0 <= jj < j && {
                    let cd = s_bytes@[jj] as u32;
                    (cd >= 65 && cd <= 90) || (cd >= 97 && cd <= 122)
                }),
                found_bad == (exists|jj: int| 0 <= jj < len_s && {
                    let cd = s_bytes@[jj] as u32;
                    let is_a = (cd >=65 && cd <=90) || (cd >=97 && cd <=122);
                    is_a && !(cd >=65 && cd <=90)
                }),
            decreases len_s - j
        {
            let code = s_bytes@[j] as u32;
            if (code >=65 && code <=90) || (code >=97 && code <=122) {
                found_alpha = true;
            }
            if (code >=65 && code <=90) || (code >=97 && code <=122) {
                if !(code >=65 && code <=90) {
                    found_bad = true;
                }
            }
            j += 1;
        }
        result.push(found_alpha && !found_bad);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}