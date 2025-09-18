// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn resize<T>(a: Vec<T>, new_size: usize) -> (result: Vec<T>)
    ensures
        result.len() == new_size,
        forall|i: int| 0 <= i < new_size ==> {
            if i < a.len() {
                result[i] == a[i]
            } else if a.len() > 0 {
                result[i] == a[(i % a.len() as int) as int]
            } else {
                true
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by changing the incorrect lemma name to the correct one, `lemma_mod_properties`. */
    let mut result = a;
    let old_len = result.len();
    let ghost original_a_view = result.view();

    if new_size <= old_len {
        result.truncate(new_size);
    } else {
        if old_len > 0 {
            result.reserve(new_size - old_len);
            let mut i = old_len;
            while i < new_size
                invariant
                    old_len <= i <= new_size,
                    result.len() == i,
                    result.view().subrange(0, old_len as int) == original_a_view,
                    forall|j: int| old_len as int <= j < i as int ==> #[trigger] result.view()[j] == original_a_view[j % (old_len as int)],
            {
                proof {
                    vstd::arithmetic::div_mod::lemma_mod_properties(i as int, old_len as int);
                }
                let val = result[(i % old_len) as usize];
                result.push(val);
                i = i + 1;
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}