// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `width as int` to `width` to match the type of `width` parameter in `ljust_element`. */
fn ljust_element(s: String, width: u8, fillchar: char) -> (result: String)
    ensures
        result@.len() == if s@.len() >= width { s@.len() } else { width as int },
        s@.len() >= width ==> result@ == s@,
        s@.len() < width ==> {
            &&& result@.len() == width as int
            &&& result@.subrange(0, s@.len() as int) == s@
            &&& forall|j: int| s@.len() as int <= j < width as int ==> result@[j] == fillchar
        }
{
    if s@.len() >= width {
        s
    } else {
        let mut new_s_bytes = s.into_bytes();
        let current_len = new_s_bytes.len();
        let padding_len: usize = (width as usize).checked_sub(current_len).unwrap_or(0);
        for _ in 0..padding_len {
            new_s_bytes.push(fillchar as u8);
        }
        String::from_utf8(new_s_bytes).unwrap()
    }
}
// </vc-helpers>

// <vc-spec>
fn ljust(a: Vec<String>, width: u8, fillchar: char) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@.len() == if a[i]@.len() >= width as nat { a[i]@.len() } else { width as nat },
        forall|i: int| 0 <= i < a.len() && a[i]@.len() >= width as nat ==> #[trigger] result[i]@ == a[i]@,
        forall|i: int| 0 <= i < a.len() && a[i]@.len() < width as nat ==> {
            &&& #[trigger] result[i]@.len() == width as nat
            &&& result[i]@.subrange(0, a[i]@.len() as int) == a[i]@
        },
        forall|i: int| 0 <= i < a.len() && a[i]@.len() == 0 ==> #[trigger] result[i]@.len() == width as nat
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Adjusted `width as int` to `width` in invariants of the while loop to match the `u8` type of `width`. */
{
    let mut result_vec: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            a.len() == old(a.len()),
            result_vec.len() == i,
            0 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result_vec[j]@.len() == if a[j]@.len() >= width { a[j]@.len() } else { width as int },
            forall|j: int| 0 <= j < i && a[j]@.len() >= width ==> #[trigger] result_vec[j]@ == a[j]@,
            forall|j: int| 0 <= j < i && a[j]@.len() < width ==> {
                &&& #[trigger] result_vec[j]@.len() == width as int
                &&& result_vec[j]@.subrange(0, a[j]@.len() as int) == a[j]@
                &&& forall|k: int| a[j]@.len() as int <= k < width as int ==> result_vec[j]@[k] == fillchar
            },
        decreases a.len() - i
    {
        let element = &a[i];
        let padded_element = ljust_element(element.clone(), width, fillchar);
        result_vec.push(padded_element);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}