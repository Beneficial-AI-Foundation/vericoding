// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): trivial proof helper kept for future use */
proof fn helpers_dummy() { }

// </vc-helpers>

// <vc-spec>
fn test_array_elements(a: &Vec<i32>, j: usize) -> (result: Vec<i32>)
    requires j < a.len(),
    ensures
        result.len() == a.len(),
        result[j as int] == 60,
        forall|k: int| 0 <= k < a.len() && k != j ==> result[k] == a[k],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): construct result by copying a and setting index j to 60 with strengthened invariant */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            res.len() == i,
            i <= a.len(),
            forall|k: int| 0 <= k < i as int ==>
                if k == j as int { res[k as int] == 60 } else { res[k as int] == a[k as int] },
        decreases a.len() - i
    {
        if i == j {
            res.push(60);
        } else {
            res.push(a[i]);
        }
        i += 1;
    }
    proof {
        assert(i == a.len());
        assert(res.len() == a.len());
        assert(res[j as int] == 60);
        assert(forall|k: int| 0 <= k < a.len() && k != j as int ==> res[k as int] == a[k as int]);
    }
    res
}

// </vc-code>

}
fn main() {}