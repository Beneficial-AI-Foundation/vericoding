use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn findMin(a: Vec<i32>, from: nat, to: nat) -> (index: nat)
    requires
        0 <= from < to <= a.len()
    ensures
        from <= index < to,
        forall|k: int| from <= k < to ==> a.spec_index(k as int) >= a.spec_index(index as int)
{
    let mut min_index = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= min_index < to,
            from < i <= to,
            forall|k: int| from <= k < i ==> a.spec_index(k as int) >= a.spec_index(min_index as int)
    {
        if a[i as usize] < a[min_index as usize] {
            min_index = i;
        }
        i = i + 1;
    }
    
    min_index
}

}