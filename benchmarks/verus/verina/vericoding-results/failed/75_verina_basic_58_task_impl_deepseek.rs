// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn double_vec_lemma(s: &Vec<i32>, i: int) 
    requires
        0 <= i <= s.len() as int,
    ensures
        forall|j: int| 0 <= j < i ==> #[trigger] s@[j] * 2 == 2 * s@[j],
    decreases i
{
    if i > 0 {
        double_vec_lemma(s, i - 1);
    }
}

proof fn arithmetic_lemma()
    ensures
        forall|x: int| x * 2 == 2 * x,
{
    assert(forall|x: int| x * 2 == 2 * x) by {
        assert(forall|x: int| x * 2 == 2 * x);
    };
}
// </vc-helpers>

// <vc-spec>
fn double_array_elements(s: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] result[i] == 2 * s[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arithmetic and added proof for invariant */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    proof {
        arithmetic_lemma();
    }
    
    while i < s.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result@[j] == 2 * s@[j],
        decreases s.len() - i
    {
        let val = s[i];
        result.push(2 * val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}