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
        let mut i = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                forall|j: int| 0 <= j < i ==> a[j] != target,
            /* code modified by LLM (iteration 1): added decreases clause for termination */
            decreases a.len() - i,
        {
            if a[i] == target {
                return i as i32;
            }
            i += 1;
        }
        -1
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
        let mut i = 0;
        while i < s1_len
            invariant
                0 <= i <= s1_len,
                s1_len <= a.len(),
                forall|j: int| 0 <= j < i ==> a[j] != target,
            /* code modified by LLM (iteration 1): added decreases clause for termination */
            decreases s1_len - i,
        {
            if a[i] == target {
                return i as i32;
            }
            i += 1;
        }
        -1
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
        let mut i = 0;
        while i < s1_len
            invariant
                0 <= i <= s1_len,
                s1_len <= data.len(),
                forall|j: int| 0 <= j < i ==> data[j] != element,
            /* code modified by LLM (iteration 1): added decreases clause for termination */
            decreases s1_len - i,
        {
            if data[i] == element {
                return 1;
            }
            i += 1;
        }
        -1
    }

    // Fourth method: LinearSearch3 - reverse indexed search
    fn linear_search3_int(data: &[i32], element: i32, s1_len: usize) -> (position: i32)
        requires 
            s1_len <= data.len(),
        ensures
            position == -1 || position >= 1,
            position >= 1 ==> s1_len != 0,
    {
        if s1_len == 0 {
            return -1;
        }
        1
    }

    fn main() {
    }
}