// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed requires/ensures from spec function */
spec fn positive_mod(a: int, n: int) -> int
{
    let r = a % n;
    if r < 0 { r + n } else { r }
}

proof fn lemma_positive_mod_bounds(a: int, n: int)
    requires n > 0
    ensures 0 <= positive_mod(a, n) < n
{
}

proof fn lemma_normalize_index_bounds(i: int, shift: int, n: int)
    requires n > 0, 0 <= i < n
    ensures 0 <= normalize_index(i, shift, n) < n
{
    lemma_positive_mod_bounds(i - shift, n);
}

fn normalize_index_exec(i: usize, shift: i32, n: usize) -> (result: usize)
    requires n > 0, i < n
    ensures result < n, result == normalize_index(i as int, shift as int, n as int)
{
    let src_idx_signed = (i as i32) - shift;
    let src_idx = if src_idx_signed >= 0 {
        (src_idx_signed as usize) % n
    } else {
        let neg_offset = ((-src_idx_signed) as usize) % n;
        if neg_offset == 0 { 0 } else { n - neg_offset }
    };
    src_idx
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
    /* code modified by LLM (iteration 5): use executable helper function instead of casting int types */
    if a.len() == 0 {
        return a;
    }
    
    let mut result = Vec::with_capacity(a.len());
    let ghost n = a.len() as int;
    
    for i in 0..a.len()
        invariant
            result.len() == i,
            n == a.len(),
            n > 0,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == a[normalize_index(j, shift as int, n)]
    {
        proof {
            let ghost i_int = i as int;
            let ghost shift_int = shift as int;
            lemma_normalize_index_bounds(i_int, shift_int, n);
        }
        let src_idx = normalize_index_exec(i, shift, a.len());
        result.push(a[src_idx]);
    }
    
    result
}
// </vc-code>


}
fn main() {}