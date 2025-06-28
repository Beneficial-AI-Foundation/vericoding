use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn mlastMaximum(v: Vec<int>) -> (i: int)
    requires
        v.len()>0
    ensures
        0<=i<v.len(),
        forall k:: 0<=k<v.len() ==> v.spec_index(i)>=v.spec_index(k),
        forall l:: i<l<v.len() ==> v.spec_index(i)>v.spec_index(l)
{
    let mut max_val = v[0];
    let mut max_idx = 0;
    let mut idx = 1;
    
    while idx < v.len()
        invariant
            0 <= max_idx < v.len(),
            1 <= idx <= v.len(),
            max_val == v.spec_index(max_idx),
            // max_val is the maximum among elements seen so far
            forall k:: 0 <= k < idx ==> v.spec_index(k) <= max_val,
            // max_idx is the last occurrence of max_val among elements seen so far
            forall k:: 0 <= k < idx && v.spec_index(k) == max_val ==> k <= max_idx,
            // elements after max_idx (among those seen so far) are strictly less than max_val
            forall l:: max_idx < l < idx ==> v.spec_index(l) < max_val,
            // max_val is at least as large as any element in the entire vector up to max_idx
            forall k:: 0 <= k <= max_idx ==> v.spec_index(k) <= max_val,
    {
        if v[idx] >= max_val {
            if v[idx] > max_val {
                max_val = v[idx];
            }
            max_idx = idx;
        }
        idx += 1;
    }
    
    // Add proof assertions to help verification
    assert(idx == v.len());
    assert(forall k:: 0 <= k < v.len() ==> v.spec_index(k) <= max_val);
    assert(forall k:: 0 <= k < v.len() && v.spec_index(k) == max_val ==> k <= max_idx);
    assert(forall l:: max_idx < l < v.len() ==> v.spec_index(l) < max_val);
    
    max_idx
}

}