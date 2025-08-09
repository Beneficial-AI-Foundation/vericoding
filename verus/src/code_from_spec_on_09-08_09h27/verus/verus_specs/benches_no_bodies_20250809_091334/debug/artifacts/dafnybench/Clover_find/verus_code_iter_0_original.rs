use vstd::prelude::*;

verus! {
    fn find(a: &[i32], key: i32) -> (index: i32)
        requires a.len() < 0x8000_0000,
        ensures
            -1 <= index < a.len(),
            index != -1 ==> 0 <= index < a.len() && a[index as int] == key && (forall|i: int| 0 <= i < index ==> a[i] != key),
            index == -1 ==> (forall|i: int| 0 <= i < a.len() ==> a[i] != key)
    {
    return 0;  // TODO: Remove this line and implement the function body
    }
}

fn main() {}