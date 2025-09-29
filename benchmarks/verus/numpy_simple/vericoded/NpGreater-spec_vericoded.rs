// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): lemma about usize-to-int ordering for bounds */
proof fn lemma_usize_lt_implies_int_lt(i: usize, n: usize)
    ensures
        i < n ==> (i as int) < (n as int),
{
}

// </vc-helpers>

// <vc-spec>
fn greater(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == (a[i] as i32 > b[i] as i32)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implement loop with proper invariants and bound assertions for safe indexing */
    let n = a.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            n == a.len(),
            n == b.len(),
            forall|j: int| 0 <= j < i as int ==> result[j] == (a[j] as i32 > b[j] as i32),
        decreases n - i
    {
        proof {
            assert(i < n);
            assert(n == a.len());
            assert(n == b.len());
            assert((i as int) < (a.len() as int));
            assert((i as int) < (b.len() as int));
        }
        let ai = a[i] as i32;
        let bi = b[i] as i32;
        let c = ai > bi;
        result.push(c);
        i = i + 1;
    }
    result
}

// </vc-code>


}
fn main() {}