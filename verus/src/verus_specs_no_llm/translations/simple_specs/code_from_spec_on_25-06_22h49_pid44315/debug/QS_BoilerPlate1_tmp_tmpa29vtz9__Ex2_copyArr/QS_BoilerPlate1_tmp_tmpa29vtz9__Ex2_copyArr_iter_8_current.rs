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
        ret@ == a@.subrange(l as int, r as int)
{
    let mut result = Vec::new();
    let mut i = l;
    
    while i < r
        invariant
            l <= i <= r,
            result.len() == (i - l) as nat,
            forall |k: int| 0 <= k < (i - l) ==> result@[k] == a@[l + k]
    {
        result.push(a[i as usize]);
        i = i + 1;
    }
    
    proof {
        // Prove the sequence equality
        assert(result@.len() == (r - l) as nat);
        assert(a@.subrange(l as int, r as int).len() == (r - l) as nat);
        
        assert forall |k: int| 0 <= k < (r - l) implies 
            result@[k] == a@.subrange(l as int, r as int)[k] by {
            // From the loop invariant when i == r
            assert(result@[k] == a@[l + k]);
            // By definition of subrange
            assert(a@.subrange(l as int, r as int)[k] == a@[l + k]);
        };
        
        // Sequences with same length and same elements are equal
        assert(result@ =~= a@.subrange(l as int, r as int));
    }
    
    result
}

}