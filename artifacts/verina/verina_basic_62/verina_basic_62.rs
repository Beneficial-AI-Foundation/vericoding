use vstd::prelude::*;

verus! {

spec fn find_precond(a: Seq<i32>, key: i32) -> bool {
    true
}

spec fn find_postcond(a: Seq<i32>, key: i32, result: i32) -> bool {
    // result is either -1 or a valid index
    (result == -1 || (result >= 0 && result < a.len() as i32))
    // if result is not -1, then a[result] == key and all elements before result are != key
    && (result != -1 ==> (a[result as int] == key && forall|i: int| 0 <= i < result ==> a[i] != key))
    // if result is -1, then no element in the array equals key
    && (result == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != key)
}

fn find(a: &Vec<i32>, key: i32) -> (result: i32)
    requires
        find_precond(a@, key),
        a.len() < 0x80000000,  // ensure we can represent all indices as i32
    ensures
        find_postcond(a@, key, result),
{
    let mut index: usize = 0;
    
    while index < a.len()
        invariant
            index <= a.len(),
            a.len() < 0x80000000,
            forall|i: int| 0 <= i < index as int ==> a@[i] != key,
        decreases a.len() - index,
    {
        if a[index] == key {
            let result = index as i32;
            assert(index < a.len());
            assert(a.len() < 0x80000000);
            assert(index < 0x80000000);
            assert(result >= 0);
            assert(result < a.len() as i32);
            assert(a@[result as int] == key);
            assert(forall|i: int| 0 <= i < result ==> a@[i] != key);
            return result;
        }
        index = index + 1;
    }
    
    assert(index == a.len());
    assert(forall|i: int| 0 <= i < a.len() ==> a@[i] != key);
    return -1;
}

} // verus!

fn main() {}