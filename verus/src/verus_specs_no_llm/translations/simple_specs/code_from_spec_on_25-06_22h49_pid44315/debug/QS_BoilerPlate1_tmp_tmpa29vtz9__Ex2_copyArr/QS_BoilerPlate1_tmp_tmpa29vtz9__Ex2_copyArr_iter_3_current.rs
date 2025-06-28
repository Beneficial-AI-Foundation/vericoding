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
            assert(i as usize < a.len());
        }
        result.push(a[i as usize]);
        i = i + 1;
    }
    
    proof {
        assert(result.len() == (r - l) as nat);
        assert(forall |k: int| 0 <= k < result.len() ==> result[k] == a[l + k]);
        assert(result.spec_index(..) =~= a.spec_index(l..r));
    }
    
    result
}

}