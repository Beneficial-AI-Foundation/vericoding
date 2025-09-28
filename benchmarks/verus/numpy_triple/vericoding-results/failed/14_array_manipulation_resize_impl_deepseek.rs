// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed modulo to properly handle ghost vs exec code */
fn modulo(a: int, b: int) -> int
    requires
        b > 0,
    ensures
        0 <= result < b,
        result == a % b
{
    if a >= 0 {
        a % b
    } else {
        (a % b + b) % b
    }
}
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
    /* code modified by LLM (iteration 5): removed ghost type conversions and fixed result variable */
    let mut result_vec = Vec::with_capacity(new_size);
    let a_len = a.len();
    
    if a_len == 0 {
        let mut i = 0;
        while i < new_size
            invariant
                0 <= i <= new_size,
                result_vec.len() == i
            decreases new_size - i
        {
            result_vec.push(unsafe { std::mem::zeroed() });
            i += 1;
        }
    } else {
        let len_int = a_len as int;
        
        let copy_len = if new_size < a_len { new_size } else { a_len };
        let mut i = 0;
        while i < copy_len
            invariant
                0 <= i <= copy_len,
                result_vec.len() == i,
                forall|j: int| 0 <= j < i ==> result_vec[j] == a[j]
            decreases copy_len - i
        {
            result_vec.push(a[i]);
            i += 1;
        }
        
        let mut j = i;
        while j < new_size
            invariant
                i <= j <= new_size,
                result_vec.len() == j,
                forall|k: int| 0 <= k < i ==> result_vec[k] == a[k],
                forall|k: int| i <= k < j ==> {
                    let idx = ((k as int) % len_int) as usize;
                    result_vec[k] == a[idx]
                }
            decreases new_size - j
        {
            let idx = ((j as int) % len_int) as usize;
            result_vec.push(a[idx]);
            j += 1;
        }
    }
    
    result_vec
}
// </vc-code>

}
fn main() {}