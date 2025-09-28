// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed ghost sequence access for subrange and len operations by using proper syntax for accessing string sequences */
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
    /* code modified by LLM (iteration 4): Fixed compilation error by correcting ghost sequence access using (result@[j])@ for string sequences and (current_ghost)@ for length */
    let mut result: Vec<String> = Vec::new();
    let width_usize: usize = width as usize;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] (result)@[j]@.len() == if (a)@[j]@.len() >= width as nat { (a)@[j]@.len() } else { width as nat },
            forall|j: int| 0 <= j < i && (a)@[j]@.len() >= width as nat ==> #[trigger] result@[j] == (a)@[j],
            forall|j: int| 0 <= j < i && (a)@[j]@.len() < width as nat ==> {
                &&& #[trigger] (result)@[j]@.len() == width as nat
                &&& (result)@[j]@.subrange(0, (a)@[j]@.len() as int) == (a)@[j]@
            },
            forall|j: int| 0 <= j < i && (a)@[j]@.len() == 0 ==> #[trigger] (result)@[j]@.len() == width as nat
        decreases a.len() - i
    {
        let current_exec = &a[i];
        let current_len_exec = current_exec.len();
        if current_len_exec >= width_usize {
            result.push(current_exec.clone());
        } else {
            let mut new_string = current_exec.clone();
            for _ in 0..(width_usize - current_len_exec) {
                new_string.push(fillchar);
            }
            result.push(new_string);
        }
        proof {
            let current_ghost = a@[i as int];
            let j = i as int;
            if (current_ghost)@.len() >= width as nat {
                assert(result@[j] == current_ghost);
            } else {
                assert((result)@[j]@.len() == width as nat);
                assert((result)@[j]@.subrange(0, (current_ghost)@.len() as int) == (current_ghost)@);
            }
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}