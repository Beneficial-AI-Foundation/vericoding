// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
spec fn all_nonzero(v: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v[i] != 0
}

fn mod_vec(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        a.len() == b.len(),
        all_nonzero(b@),
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == a[i] % b[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): changed loop index to int and used sequence view length to avoid type mismatches */
    let n = a@.len();
    let mut i: int = 0;
    let mut result = Vec::new();
    while i < n
        invariant
            0 <= i <= n,
            n == a@.len(),
            n == b@.len(),
            result.len() == i as usize,
            all_nonzero(b@),
            forall|j: int| 0 <= j < i ==> 
                #[trigger] result@[j] == a@[j] % b@[j],
        decreases n - i
    {
        proof {
            assert(0 <= i < b@.len());
            assert(all_nonzero(b@));
            assert(b@[i] != 0);
        }
        result.push(a[i as usize] % b[i as usize]);
        proof {
            assert(result@[i] == a[i as usize] % b[i as usize]);
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}