// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation error by adding return type annotation */
fn mod_positive(x: int, n: int) -> (r: int)
    requires n > 0,
    ensures 0 <= r < n,
    ensures x % n == r
{
    let mut r = x % n;
    if r < 0 {
        r = r + n;
    }
    r
}

proof fn translation_invariance(a: Seq<i32>, n: int, offset: int, i: int)
    requires n > 0, 0 <= i < n,
    ensures (i + offset) % n == ((i % n) + offset) % n
{
}
// </vc-helpers>

// <vc-spec>
fn rotate(a: &Vec<i32>, offset: int) -> (result: Vec<i32>)
    requires offset >= 0,
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let src_idx = (i + offset) % (a.len() as int);
            #[trigger] result[i] == a[src_idx]
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by adding return type annotation */
{
    let n = a.len() as int;
    let mut result = Vec::with_capacity(a.len());
    
    let ghost a_seq = a@;
    
    proof {
        translation_invariance(a_seq, n, offset, 0);
    }
    
    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i as usize,
            forall|j: int| 0 <= j < i ==> {
                let src_idx = mod_positive(j + offset, n);
                #[trigger] result@[j] == a_seq[src_idx]
            }
        decreases a.len() - i
    {
        let src_idx = mod_positive((i as int) + offset, n) as usize;
        result.push(a[src_idx]);
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}