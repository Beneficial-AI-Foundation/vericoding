// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added to fix sequence handling and type issues */
spec fn get_chars_to_strip(chars: Option<String>) -> Seq<char> {
    if chars.is_Some() {
        chars.unwrap()@
    } else {
        seq![' ', '\t', '\n', '\r']
    }
}
// </vc-helpers>

// <vc-spec>
fn rstrip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() <= a[i]@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed type mismatches with nat/int, improper sequence indexing, invalid push_char method, and for-loop over sequence by using range and @ indexing */
    let mut result: Vec<String> = Vec::new();
    let chars_to_strip_seq = get_chars_to_strip(chars);
    for i in 0..a.len() {
        let s = &a[i];
        let s_seq = s@;
        let mut new_end: int = s_seq.len() as int;
        while new_end > 0 {
            let c = s_seq@[ (new_end - 1) as int ];
            let mut is_to_strip = false;
            for j in 0..chars_to_strip_seq.len() {
                let ch = chars_to_strip_seq@[j];
                if ch == c {
                    is_to_strip = true;
                    break;
                }
            }
            if !is_to_strip {
                break;
            }
            new_end = new_end - 1;
        }
        let mut new_s = String::new();
        for j in 0..new_end {
            new_s.push(s_seq@[j]);
        }
        result.push(new_s);
    }
    result
}
// </vc-code>

}
fn main() {}