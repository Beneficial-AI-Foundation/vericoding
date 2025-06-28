use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Find(blood: Vec<int>, key: int) -> (index: int)
    requires
        true  // Vec is never null in Rust, so this is always true
    ensures
        0 <= index ==> index < blood.len() && blood.spec_index(index) == key,
        index < 0 ==> forall k: int :: 0 <= k < blood.len() ==> blood.spec_index(k) != key
{
    let mut i: usize = 0;
    
    while i < blood.len()
        invariant
            0 <= i <= blood.len(),
            forall k: int :: 0 <= k < i ==> blood.spec_index(k) != key
    {
        if blood[i] == key {
            assert(i < blood.len());
            assert(blood.spec_index(i as int) == key);
            assert(0 <= i as int);
            assert(i as int < blood.len());
            return i as int;
        }
        
        assert(blood.spec_index(i as int) != key);
        i = i + 1;
    }
    
    assert(i == blood.len());
    assert(forall k: int :: 0 <= k < blood.len() ==> blood.spec_index(k) != key);
    return -1;
}

}