use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn Find(blood: &Vec<int>, key: int) -> (index: int)
    requires
        true  // Vec is never null in Rust, so this is always true
    ensures
        index >= 0 ==> index < blood.len() && blood.spec_index(index) == key,
        index < 0 ==> forall |k: int| 0 <= k < blood.len() ==> blood.spec_index(k) != key
{
    let mut i: usize = 0;
    
    while i < blood.len()
        invariant
            0 <= i <= blood.len(),
            forall |k: int| 0 <= k < i ==> blood.spec_index(k) != key
    {
        if blood.spec_index(i as int) == key {
            return i as int;
        }
        
        i = i + 1;
    }
    
    return -1;
}

}