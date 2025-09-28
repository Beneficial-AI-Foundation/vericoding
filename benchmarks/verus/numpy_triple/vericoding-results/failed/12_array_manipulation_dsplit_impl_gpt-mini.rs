// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove i*(arr_len/sections)+j < arr_len */
proof fn index_within(arr_len: usize, sections: usize, i: usize, j: usize)
    requires
        sections > 0,
        arr_len % sections == 0,
        i < sections,
        j < arr_len / sections,
    ensures
        i * (arr_len / sections) + j < arr_len,
    decreases
        arr_len
{
    let k = arr_len / sections;
    let ai: int = i as int;
    let aj: int = j as int;
    let ak: int = k as int;
    let asections: int = sections as int;
    let aarr: int = arr_len as int;

    // from j < k we get ak > 0
    assert(aj < ak);
    assert(aj >= 0);
    assert(ak > 0);

    // ai < asections implies ai <= asections - 1
    assert(ai < asections);
    assert(ai <= asections - 1);

    // aj < ak implies aj <= ak - 1
    assert(aj <= ak - 1);

    // combine bounds to get ai*ak + aj < asections*ak
    assert(ai * ak + aj <= (asections - 1) * ak + (ak - 1));
    assert((asections - 1) * ak + (ak - 1) == asections * ak - 1);
    assert(ai * ak + aj < asections * ak);

    // use division relation: arr_len == k*sections + rem, rem >= 0
    let rem: int = (arr_len % sections) as int;
    assert(aarr == ak * asections + rem);
    assert(rem >= 0);
    assert(asections * ak <= aarr);

    assert(ai * ak + aj < aarr);
}

// </vc-helpers>

// <vc-spec>
fn dsplit(arr: Vec<f32>, sections: usize) -> (result: Vec<Vec<f32>>)
    requires 
        sections > 0,
        arr.len() % sections == 0,
    ensures
        result.len() == sections,
        forall|i: int| 0 <= i < sections ==> result[i].len() == arr.len() / sections,
        forall|i: int, j: int| 0 <= i < sections && 0 <= j < (arr.len() / sections) ==> 
            result[i][j] == arr[i * (arr.len() / sections) + j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build sections of the array with loop invariants and use index_within */
    let n = arr.len();
    let chunk = n / sections;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < sections
        invariant
            result.len() == i,
            forall|a: int| 0 <= a < i as int ==> result[a].len() == chunk,
            i <= sections,
        decreases sections - i
    {
        let mut inner: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < chunk
            invariant
                inner.len() == j,
                forall|b: int| 0 <= b < j as int ==> inner[b] == arr[(i as int) * (chunk as int) + b],
                j <= chunk,
            decreases chunk - j
        {
            proof {
                // use the helper to prove the index into arr is within bounds
                index_within(n, sections, i, j);
            }
            inner.push(arr[i * chunk + j]);
            j += 1;
        }
        result.push(inner);
        i += 1;
    }
    result
}

// </vc-code>

}
fn main() {}