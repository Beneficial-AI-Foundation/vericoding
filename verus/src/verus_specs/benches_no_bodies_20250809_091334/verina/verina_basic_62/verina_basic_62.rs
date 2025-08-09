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
    return 0;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}