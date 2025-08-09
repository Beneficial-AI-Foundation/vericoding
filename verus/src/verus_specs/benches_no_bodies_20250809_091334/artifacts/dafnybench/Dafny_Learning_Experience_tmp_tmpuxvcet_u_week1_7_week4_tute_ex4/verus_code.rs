use vstd::prelude::*;

verus! {
    // First method: LinearSearch - for integer arrays
    fn linear_search_int(a: &[i32], target: i32) -> (n: i32)
        requires true,
        ensures
            -1 <= n < a.len(),
            n == -1 || a[n as int] == target,
            n != -1 ==> forall|i: int| 0 <= i < n ==> a[i] != target,
            n == -1 ==> forall|i: int| 0 <= i < a.len() ==> a[i] != target
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    // Second method: LinearSearch1 - search with length constraint
    fn linear_search1_int(a: &[i32], target: i32, s1_len: usize) -> (n: i32)
        requires 
            s1_len <= a.len(),
        ensures
            -1 <= n < a.len(),
            n == -1 || a[n as int] == target,
            n != -1 ==> forall|i: int| 0 <= i < n ==> a[i] != target,
            n == -1 ==> forall|i: int| 0 <= i < s1_len ==> a[i] != target
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    // Third method: LinearSearch2 - reverse search
    fn linear_search2_int(data: &[i32], element: i32, s1_len: usize) -> (position: i32)
        requires 
            s1_len <= data.len(),
        ensures
            position == -1 || position >= 1,
            position >= 1 ==> exists|i: int| 0 <= i < s1_len && data[i] == element,
            position == -1 ==> forall|i: int| 0 <= i < s1_len ==> data[i] != element
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    // Fourth method: LinearSearch3 - reverse indexed search
    fn linear_search3_int(data: &[i32], element: i32, s1_len: usize) -> (position: i32)
        requires 
            s1_len <= data.len(),
        ensures
            position == -1 || position >= 1,
            position >= 1 ==> s1_len != 0,
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    fn main() {
    // TODO: Remove this comment and implement the function body
    }
}