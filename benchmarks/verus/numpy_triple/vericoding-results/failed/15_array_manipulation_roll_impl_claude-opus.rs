// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added exec function for index normalization */
fn normalize_index_exec(i: usize, shift: i32, n: usize) -> (result: usize)
    requires n > 0
    ensures result < n,
            result as int == normalize_index(i as int, shift as int, n as int)
{
    let n_i32 = n as i32;
    let i_i32 = i as i32;
    let src_idx = i_i32 - shift;
    let mod_result = src_idx % n_i32;
    let normalized = if mod_result < 0 { mod_result + n_i32 } else { mod_result };
    normalized as usize
}
// </vc-helpers>

// <vc-spec>
spec fn normalize_index(i: int, shift: int, n: int) -> int {
    let src_idx = i - shift;
    let mod_result = src_idx % n;
    if mod_result < 0 { mod_result + n } else { mod_result }
}

fn roll<T>(a: Vec<T>, shift: i32) -> (result: Vec<T>)
    ensures
        result.len() == a.len(),
        a.len() == 0 ==> result@ == a@,
        a.len() > 0 ==> forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i] == a[normalize_index(i, shift as int, a.len() as int)]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added Clone trait bound and using clone() to fix move error */
    let n = a.len();
    if n == 0 {
        return a;
    }
    
    let mut result = Vec::new();
    
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            n == a.len(),
            n > 0,
            forall|j: int| 0 <= j < i ==> result@[j] == a@[normalize_index(j, shift as int, n as int)],
        decreases n - i
    {
        let src_idx = normalize_index_exec(i, shift, n);
        result.push(a[src_idx].clone());
        
        proof {
            assert(src_idx < n);
            assert(src_idx as int == normalize_index(i as int, shift as int, n as int));
            assert(result@[i as int] == a@[src_idx as int]);
            assert(result@[i as int] == a@[normalize_index(i as int, shift as int, n as int)]);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}