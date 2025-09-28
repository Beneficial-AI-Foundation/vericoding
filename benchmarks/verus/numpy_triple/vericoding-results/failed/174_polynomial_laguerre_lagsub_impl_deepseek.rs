// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

fn lagsub_lemma(c1: &Vec<i8>, c2: &Vec<i8>, i: int)
    requires
        0 <= i < c1.len(),
        c1.len() == c2.len(),
    ensures
        (#[trigger] c1@[i]) as int - (#[trigger] c2@[i]) as int == (c1[i] as int) - (c2[i] as int),
{
}

fn ensure_diff_in_i8_range(c1_val: i8, c2_val: i8) -> (diff: i8)
    ensures diff as int == (c1_val as int) - (c2_val as int),
{
    proof {
        let diff_val = (c1_val as int) - (c2_val as int);
        assert(diff_val >= i8::MIN as int);
        assert(diff_val <= i8::MAX as int);
    }
    (c1_val - c2_val) as i8
}

// </vc-helpers>

// <vc-spec>
fn lagsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires c1.len() == c2.len(),
    ensures 
        result.len() == c1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == c1[i] as int - c2[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type mismatch in lagsub_lemma call */
    let mut result = Vec::new();
    let n = c1.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == c1@[j] as int - c2@[j] as int,
        decreases n - i,
    {
        proof { lagsub_lemma(&c1, &c2, i as int); }
        let diff = c1[i] - c2[i];
        result.push(diff);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}