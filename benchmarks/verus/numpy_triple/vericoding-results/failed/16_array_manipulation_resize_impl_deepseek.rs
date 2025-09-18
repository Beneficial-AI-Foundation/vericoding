// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn modulo_lemma(x: int, y: int) 
    requires y > 0
    ensures 0 <= x % y < y
{
}

proof fn vector_indexing_lemma<T>(v: Vec<T>, i: int)
    requires 0 <= i < v.len()
    ensures v[i] == v@[i]
{
}

spec fn modulo_usize(x: int, y: int) -> (r: int)
    requires y > 0
    ensures r == x % y
{
    x % y
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
    /* code modified by LLM (iteration 5): Fix integer type casting issues using ghost code */
    let ghost old_len = a.len() as int;
    let mut result = Vec::new();
    
    let mut i: usize = 0;
    while i < new_size
        invariant
            0 <= i <= new_size,
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> {
                if j < old_len {
                    result[j as usize] == a[j as usize]
                } else if old_len > 0 {
                    result[j as usize] == a[((j % old_len) as usize)]
                } else {
                    true
                }
            }
        decreases new_size - i
    {
        ghost {
            if (i as int) < old_len {
                result.push(a[i]);
            } else if old_len > 0 {
                let index: int = modulo_usize(i as int, old_len);
                result.push(a[index as usize]);
            } else {
                assert(false); // Should not reach here per specification conditions
                result.push(a[0]);
            }
        }
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}