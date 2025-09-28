// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma syntax */
lemma lemma_no_overflow(a: i32, b: i32)
    requires
        a as int + b as int <= 2147483647,
        a as int + b as int >= -2147483648,
    ensures
        (a + b) as int == a as int + b as int
{
}
// </vc-helpers>

// <vc-spec>
spec fn prefix_sum(a: Seq<i32>, i: int) -> int
    decreases i
{
    if i < 0 || i >= a.len() {
        0
    } else if i == 0 {
        a[0] as int
    } else {
        prefix_sum(a, i - 1) + (a[i] as int)
    }
}

fn numpy_cumsum(a: Vec<i32>) -> (result: Vec<i32>)
    ensures 
        result.len() == a.len(),
        a.len() > 0 ==> result[0] == a[0],
        forall|i: int| 0 < i < a.len() ==> result[i] == result[i - 1] + a[i],
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == prefix_sum(a@, i)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added overflow checks and fixed proof */
    if a.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::with_capacity(a.len());
    result.push(a[0]);
    
    let mut i = 1;
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            result.len() > 0,
            result[0] == a[0],
            forall|j: int| 0 < j < i ==> result[j] == result[j - 1] + a[j],
            forall|j: int| 0 <= j < i ==> result[j] as int == prefix_sum(a@, j),
        decreases a.len() - i
    {
        assert(i >= 1);
        assert(i - 1 < result.len());
        assert(result[i - 1] as int + a[i] as int <= 2147483647);
        assert(result[i - 1] as int + a[i] as int >= -2147483648);
        
        let next_val = result[i - 1] + a[i];
        result.push(next_val);
        
        proof {
            lemma_no_overflow(result[i - 1], a[i]);
            assert(next_val as int == result[i - 1] as int + a[i] as int);
            assert(result@[i as int] == next_val);
            assert(result@[i as int - 1] as int == prefix_sum(a@, i as int - 1));
            assert(prefix_sum(a@, i as int) == prefix_sum(a@, i as int - 1) + a@[i as int] as int);
            assert(result@[i as int] as int == prefix_sum(a@, i as int));
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}