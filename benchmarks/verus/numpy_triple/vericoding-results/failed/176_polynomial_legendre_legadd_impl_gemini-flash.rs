// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): The `val1` and `val2` variables are declared as `int` in ghost code (within the ensures block), which is allowed. The values `s1[index]` and `s2[index]` are read from `i8` vectors, but then cast to `int` for calculation. The final `sum` is cast back to `i8`. */
fn sum_digits_at_index(s1: Seq<i8>, s2: Seq<i8>, index: int) -> (sum: i8)
    requires
        0 <= index,
    ensures
        ({ let val1: int = if index@ < s1.len() { s1[index@] as int } else { 0 };
        let val2: int = if index@ < s2.len() { s2[index@] as int } else { 0 };
        sum as int == val1 + val2})
{
    let val1: int = if index@ < s1.len() { s1[index@] as int } else { 0 };
    let val2: int = if index@ < s2.len() { s2[index@] as int } else { 0 };
    (val1 + val2) as i8
}
// </vc-helpers>

// <vc-spec>
fn legadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result@.len() == if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() },
        forall|i: int| 0 <= i < result@.len() ==> {
            let val1: int = if i < c1@.len() { c1@[i] as int } else { 0 };
            let val2: int = if i < c2@.len() { c2@[i] as int } else { 0 };
            #[trigger] result@[i] as int == val1 + val2
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The `val1` and `val2` variables within the loop invariant were declared as `int` directly, which is allowed as they are part of a ghost context (the invariant block). The `sum_digits_at_index` helper already correctly handles `int` casts. */
{
    let mut result_vec = Vec::<i8>::new();
    let max_len = if c1@.len() >= c2@.len() { c1@.len() } else { c2@.len() };

    let mut i: nat = 0;
    while (i as int) < (max_len as int)
        invariant
            0 <= i as int,
            max_len as int >= 0,
            i as int <= max_len as int,
            result_vec@.len() == i as int,
            forall|j: int| 0 <= j && j < i as int ==> {
                let val1: int = if j < c1@.len() { c1@[j] as int } else { 0 };
                let val2: int = if j < c2@.len() { c2@[j] as int } else { 0 };
                #[trigger] result_vec@[j] as int == val1 + val2
            }
        decreases max_len - (i as int)
    {
        let sum = sum_digits_at_index(c1@, c2@, i as int);
        result_vec.push(sum);
        i = i + 1;
    }
    result_vec
}
// </vc-code>


}
fn main() {}