// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adding braces to the helper function definition. */
fn to_vec_spec<T>(s: &Vec<T>) -> (out: Vec<T>)
    ensures
        out@ == s@,
        out.len() == s.len()
{
    // This is a specification function, so it doesn't need an implementation.
    // We are just defining its behavior for verification purposes.
    return *s;
}
// </vc-helpers>

// <vc-spec>
spec fn is_sign_char(c: char) -> bool {
    c == '+' || c == '-'
}

spec fn all_zeros(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

spec fn max_usize(a: usize, b: usize) -> usize {
    if a >= b { a } else { b }
}

fn zfill(a: Vec<Vec<char>>, width: usize) -> (result: Vec<Vec<char>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i].len() == max_usize(a[i].len(), width),
        forall|i: int| 0 <= i < result.len() && a[i].len() >= width ==> 
            #[trigger] result[i]@ == a[i]@,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width && a[i].len() > 0 && 
            !is_sign_char(a[i]@[0]) ==> 
            #[trigger] all_zeros(result[i]@.take((width - a[i].len()) as int)) &&
            result[i]@.skip((width - a[i].len()) as int) == a[i]@,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width && a[i].len() > 0 && 
            is_sign_char(a[i]@[0]) ==> 
            #[trigger] result[i]@[0] == a[i]@[0] &&
            result[i]@.skip(width as int) == a[i]@.skip(1),
        forall|i: int| 0 <= i < result.len() && a[i].len() == 0 ==> 
            #[trigger] result[i].len() == width && 
            all_zeros(result[i]@),
        forall|i: int| 0 <= i < result.len() && a[i].len() < width ==> 
            #[trigger] result[i].len() == width,
        forall|i: int| 0 <= i < result.len() && a[i].len() < width ==> 
            #[trigger] all_zeros(result[i]@.take((width - a[i].len()) as int))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced unsupported `to_vec()` with `to_vec_spec()` in helper for loop invariant. */
{
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut i: usize = 0;

    while i < a.len()
        invariant
            result.len() == i,
            a.len() >= i,
            forall|j: int| 0 <= j < i ==> result[j].len() == max_usize(a[j].len(), width),
            forall|j: int| 0 <= j < i && a[j].len() >= width ==> result[j]@ == a[j]@,
            forall|j: int| 0 <= j < i && a[j].len() < width && a[j].len() > 0 && 
                !is_sign_char(a[j]@[0]) ==> 
                all_zeros(result[j]@.take((width - a[j].len()) as int)) &&
                result[j]@.skip((width - a[j].len()) as int) == a[j]@,
            forall|j: int| 0 <= j < i && a[j].len() < width && a[j].len() > 0 && 
                is_sign_char(a[j]@[0]) ==> 
                result[j]@[0] == a[j]@[0] &&
                all_zeros(result[j]@.skip(1).take((width - a[j].len() - 1) as int)) &&
                result[j]@.skip((width - a[j].len() + 1) as int) == a[j]@.skip(1),
            forall|j: int| 0 <= j < i && a[j].len() == 0 ==> 
                result[j].len() == width && all_zeros(result[j]@),
            forall|j: int| 0 <= j < i && a[j].len() < width ==> 
                result[j].len() == width,
            forall|j: int| 0 <= j < i && a[j].len() < width ==> 
                all_zeros(result[j]@.take((width - a[j].len()) as int))
        decreases a.len() - i
    {
        let current_elem = to_vec_spec(&a[i]); // Use the specification-aware to_vec
        let current_len = current_elem.len();
        let mut new_elem: Vec<char> = Vec::new();

        if current_len >= width {
            new_elem = current_elem;
        } else {
            let pad_len = width - current_len;
            if current_len == 0 {
                for _ in 0..width {
                    new_elem.push('0');
                }
            } else if is_sign_char(current_elem[0]) {
                new_elem.push(current_elem[0]);
                for _ in 0..pad_len {
                    new_elem.push('0');
                }
                for k in 1..current_len {
                    new_elem.push(current_elem[k]);
                }
            } else {
                for _ in 0..pad_len {
                    new_elem.push('0');
                }
                for k in 0..current_len {
                    new_elem.push(current_elem[k]);
                }
            }
        }
        result.push(new_elem);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}