use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn findMin(a: Vec<real>, from: nat, to: nat) -> (index: nat)
    requires
        0 <= from < to <= a.len()
    ensures
        from <= index < to,
        forall k :: from <= k < to ==> a.spec_index(k) >= a.spec_index(index)
{
    let mut min_index = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= min_index < to,
            from < i <= to,
            forall k :: from <= k < i ==> a.spec_index(k) >= a.spec_index(min_index)
    {
        if a[i] < a[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    
    min_index
}

}