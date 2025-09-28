// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple spec mapping to sequence membership */
spec fn vec_contains(s: &Vec<i8>, x: i8) -> bool {
    s@.contains(x)
}
// </vc-helpers>

// <vc-spec>
fn unique(s: Vec<i8>) -> (result: Vec<i8>)
    ensures
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> (result@[i] as int) < (result@[j] as int) &&
        forall|x: i8| result@.contains(x) ==> s@.contains(x) &&
        forall|x: i8| s@.contains(x) ==> result@.contains(x)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): scan all i8 values and build sorted unique result; fix seq indexing types */
    let mut result: Vec<i8> = Vec::new();
    let mut u: usize = 0;
    while u < 256
        invariant
            forall|i: int, j: int| 0 <= i < j < result@.len() ==> (result@[i] as int) < (result@[j] as int),
            forall|x: i8| result@.contains(x) ==> s@.contains(x),
            forall|x: i8| s@.contains(x) && (x as int) < (u as int - 128) ==> result@.contains(x),
            forall|x: i8| result@.contains(x) ==> (x as int) < (u as int - 128),
        decreases 256 - (u as int)
    {
        let k: i8 = ((u as i32) - 128) as i8;
        let mut found: bool = false;
        let mut j: usize = 0;
        let len: usize = s.len();
        while j < len
            invariant
                j <= len,
                found == exists|jj: int| 0 <= jj < (j as int) && s@[jj] == k,
            decreases (len as int) - (j as int)
        {
            let v = *s.get(j).unwrap();
            if v == k {
                found = true;
            }
            j += 1;
        }
        if found {
            result.push(k);
        }
        u += 1;
    }
    result
}
// </vc-code>


}

fn main() {}