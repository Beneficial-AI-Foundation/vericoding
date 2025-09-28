// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): track mathematical sum in ghost state for verification */
    let mut result = Vec::new();
    if a.len() == 0 {
        return result;
    }
    
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            i <= a.len(),
            forall|j: int| 0 <= j < i ==> result[j] as int == prefix_sum(a@, j),
            i == 0 || result[i - 1] as int == prefix_sum(a@, (i - 1) as int),
        decreases a.len() - i
    {
        if i == 0 {
            sum = a[i];
        } else {
            sum = result[i - 1] + a[i];
        }
        result.push(sum);
        
        assert(result[i as int] as int == prefix_sum(a@, i as int)) by {
            if i == 0 {
                assert(result[0] as int == a@[0] as int);
                assert(prefix_sum(a@, 0) == a@[0] as int);
            } else {
                assert(result[i as int] as int == result[(i - 1) as int] as int + a@[i as int] as int);
                assert(result[(i - 1) as int] as int == prefix_sum(a@, (i - 1) as int));
                assert(prefix_sum(a@, i as int) == prefix_sum(a@, (i - 1) as int) + a@[i as int] as int);
            }
        }
        
        i = i + 1;
    }
    
    assert(a.len() > 0 ==> result[0] == a[0]);
    
    assert(forall|j: int| 0 < j < result.len() ==> result[j] == result[j - 1] + a[j]) by {
        assert forall|j: int| 0 < j < result.len() implies result[j] == result[j - 1] + a[j] by {
            assert(result[j] as int == prefix_sum(a@, j));
            assert(result[j - 1] as int == prefix_sum(a@, j - 1));
            assert(prefix_sum(a@, j) == prefix_sum(a@, j - 1) + a@[j] as int);
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}