// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compilation error by using s.len() which is spec'd in Verus */
fn string_ljust(s: String, width: u8, fillchar: char) -> (result: String)
    ensures
        result@.len() == if s@.len() >= width as nat { s@.len() } else { width as nat },
        s@.len() >= width as nat ==> result@ == s@,
        s@.len() < width as nat ==> {
            &&& result@.len() == width as nat
            &&& result@.subrange(0, s@.len() as int) == s@
            &&& forall|i: int| s@.len() as int <= i < width as int ==> result@[i] == fillchar
        },
{
    let s_len = s.len();
    let width_usize = width as usize;
    if s_len >= width_usize {
        s
    } else {
        let mut new_s = s;
        let num_to_add = width_usize - s_len;
        let mut i: usize = 0;
        while i < num_to_add
            invariant
                (width as nat) > s@.len(),
                s_len as nat == s@.len(),
                num_to_add == width_usize - s_len,
                i <= num_to_add,
                new_s@.len() == s@.len() + (i as nat),
                new_s@.subrange(0, s@.len() as int) == s@,
                forall|j: int| s@.len() as int <= j < (s@.len() + (i as nat)) as int ==> new_s@[j] == fillchar,
            decreases num_to_add - i
        {
            new_s.push(fillchar);
            i = i + 1;
        }
        new_s
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
{
    /* code modified by LLM (iteration 5): retained correct logic which relies on the fixed helper function */
    let mut result_vec: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result_vec.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                let original_s = a[j]@;
                let new_s = result_vec[j]@;
                &&& #[trigger] new_s.len() == if original_s.len() >= width as nat { original_s.len() } else { width as nat }
                &&& (original_s.len() >= width as nat ==> new_s == original_s)
                &&& (original_s.len() < width as nat ==> {
                    &&& new_s.len() == width as nat
                    &&& new_s.subrange(0, original_s.len() as int) == original_s
                    &&& forall|k: int| original_s.len() as int <= k < width as int ==> new_s[k] == fillchar
                })
            },
        decreases a.len() - i
    {
        let s_new = string_ljust(a[i].clone(), width, fillchar);
        result_vec.push(s_new);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}