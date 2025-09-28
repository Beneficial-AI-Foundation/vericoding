// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed */
// </vc-helpers>

// <vc-spec>
spec fn is_whitespace_char(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
}

spec fn all_chars_whitespace(s: Seq<char>) -> bool 
    decreases s.len()
{
    if s.len() == 0 {
        true
    } else {
        is_whitespace_char(s[0]) && all_chars_whitespace(s.skip(1))
    }
}

fn isspace(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> 
            result[i] == (a[i]@.len() > 0 && all_chars_whitespace(a[i]@)),
        forall|i: int| 0 <= i < a.len() ==> 
            (a[i]@.len() == 0 ==> result[i] == false),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed type of index access on current_string_seq to usize */
{
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            result.len() == i,
            result.len() <= a.len(),
            forall|j: int| 0 <= j < i as int ==> result[j] == (a[j as usize].view().len() > 0 && all_chars_whitespace(a[j as usize].view())),
        decreases a.len() - i
    {

        let current_string_seq = a[i].view();
        let mut all_ws = true;
        let mut k: usize = 0;

        while k < current_string_seq.len()
            invariant
                all_ws ==> forall|l: int| 0 <= l < k as int ==> is_whitespace_char(current_string_seq.broadcast_object_to_ref().index(l as int)),
                !all_ws ==> exists|l: int| 0 <= l < k as int && !is_whitespace_char(current_string_seq.broadcast_object_to_ref().index(l as int)),
                k <= current_string_seq.len(),
            decreases current_string_seq.len() - k
        {
            if !is_whitespace_char(current_string_seq.broadcast_object_to_ref().index(k)) {
                all_ws = false;
            }
            k = k + 1;
        }

        if all_ws && current_string_seq.len() > 0 {
             result.push(true);
        } else {
             result.push(false);
        }
       
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}