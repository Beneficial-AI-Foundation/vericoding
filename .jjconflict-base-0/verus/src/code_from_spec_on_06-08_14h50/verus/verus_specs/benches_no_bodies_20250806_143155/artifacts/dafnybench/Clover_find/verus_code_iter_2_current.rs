use vstd::prelude::*;

verus! {
    fn find(a: &[i32], key: i32) -> (index: i32)
        requires a.len() < 0x8000_0000,
        ensures
            -1 <= index < a.len(),
            index != -1 ==> 0 <= index < a.len() && a[index as int] == key && (forall|i: int| 0 <= i < index ==> a[i] != key),
            index == -1 ==> (forall|i: int| 0 <= i < a.len() ==> a[i] != key)
    {
        let mut i = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                forall|j: int| 0 <= j < i ==> a[j] != key,
            /* code modified by LLM (iteration 1): Added decreases clause to ensure loop termination */
            decreases a.len() - i,
        {
            if a[i] == key {
                return i as i32;
            }
            i += 1;
        }
        return -1;
    }
}

fn main() {}