use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn copyArr(a: Vec<int>, l: int, r: int) -> (ret: Vec<int>)
    requires
        0 <= l < r <= a.len()
    ensures
        ret.len() == (r - l) as nat,
        ret.spec_index(..) == a.spec_index(l..r)
{
    let mut result = Vec::new();
    let mut i = l;
    
    while i < r
        invariant
            l <= i <= r,
            result.len() == (i - l) as nat,
            forall |k: int| l <= k < i ==> result[k - l] == a[k]
    {
        proof {
            assert(0 <= i < a.len());
        }
        result.push(a[i]);
        i = i + 1;
    }
    
    proof {
        assert(result.len() == (r - l) as nat);
        
        // Prove the sequence equality by showing each element is equal
        assert forall |k: int| 0 <= k < (r - l) implies 
            result.spec_index(..)[k] == a.spec_index(l..r)[k] by {
            // From the loop invariant, we know result[k] == a[l + k]
            assert(result[k] == a[l + k]);
            // And a.spec_index(l..r)[k] == a[l + k] by definition of subrange
            assert(a.spec_index(l..r)[k] == a[l + k]);
            // Therefore they are equal
        };
        
        // The sequences have the same length and same elements, so they are equal
        assert(result.spec_index(..).len() == a.spec_index(l..r).len());
    }
    
    result
}

}