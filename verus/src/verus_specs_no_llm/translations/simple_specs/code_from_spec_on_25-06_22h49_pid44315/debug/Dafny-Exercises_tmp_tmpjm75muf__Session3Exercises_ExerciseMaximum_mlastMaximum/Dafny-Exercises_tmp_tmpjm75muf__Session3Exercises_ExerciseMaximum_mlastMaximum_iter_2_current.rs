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
            forall k:: 0 <= k < idx ==> v.spec_index(k) <= max_val,
            forall k:: 0 <= k < idx && v.spec_index(k) == max_val ==> k <= max_idx,
            forall l:: max_idx < l < idx ==> v.spec_index(max_idx) > v.spec_index(l),
    {
        if v[idx] > max_val {
            max_val = v[idx];
            max_idx = idx;
        }
        idx += 1;
    }
    
    max_idx
}

}