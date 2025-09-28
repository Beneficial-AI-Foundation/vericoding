// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added ghost helper to get string length as nat */
spec fn string_len_as_nat(s: String) -> nat
{
    s@.len()
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
{
    /* code modified by LLM (iteration 5): use exec code with proof blocks for verification */
    let mut result: Vec<String> = Vec::new();
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j]@.len() == if a[j]@.len() >= width as nat { a[j]@.len() } else { width as nat },
            forall|j: int| 0 <= j < i && a[j]@.len() >= width as nat ==> result[j]@ == a[j]@,
            forall|j: int| 0 <= j < i && a[j]@.len() < width as nat ==> {
                &&& result[j]@.len() == width as nat
                &&& result[j]@.subrange(0, a[j]@.len() as int) == a[j]@
            },
            forall|j: int| 0 <= j < i && a[j]@.len() == 0 ==> result[j]@.len() == width as nat,
    {
        let s = &a[i];
        let padded_string = if s.len() >= width as usize {
            s.clone()
        } else {
            let padding_needed = width as usize - s.len();
            let mut padded = s.clone();
            let mut j = 0;
            while j < padding_needed
                invariant
                    j <= padding_needed,
                    padding_needed == width as usize - s.len(),
                    padded@.len() == s@.len() + j,
                    padded@.subrange(0, s@.len() as int) == s@,
            {
                padded.push(fillchar);
                j += 1;
            }
            padded
        };
        result.push(padded_string);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}