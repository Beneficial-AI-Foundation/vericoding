// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): No changes needed for helpers */
// </vc-helpers>

// <vc-spec>
fn cum_sum(a: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> result[i as int] as int == result[(i - 1) as int] as int + a[i as int] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Fixed type mismatches by using spec indexing with int for overflow assertions */
    let mut result = Vec::with_capacity(a.len());
    result.push(a[0]);
    let mut i: usize = 1;
    
    proof {
        assert(result@[0] == a@[0]);
    }
    
    while i < a.len()
        invariant
            result.len() == i,
            result@.len() == i,
            forall|j: int| 0 <= j < (i as int) ==> 
                if j == 0 { 
                    result@[j] as int == a@[j] as int 
                } else { 
                    result@[j] as int == result@[j - 1] as int + a@[j] as int 
                },
        decreases a.len() - i
    {
        assert((result@[ (i - 1) as int ] as int + a@[ i as int ] as int) <= (i8::MAX as int) 
            && (result@[ (i - 1) as int ] as int + a@[ i as int ] as int) >= (i8::MIN as int));
        result.push(result[i - 1] + a[i]);
        proof {
            assert(result@[i as int] as int == result@[ (i as int) - 1] as int + a@[i as int] as int);
        }
        i = i + 1;
    }
    
    proof {
        assert(result@.len() == a.len() as int);
        assert(forall|k: int| 1 <= k < (a.len() as int) ==> result@[k] as int == result@[k - 1] as int + a@[k] as int);
    }
    
    result
}
// </vc-code>


}
fn main() {}