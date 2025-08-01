use vstd::prelude::*;

verus! {
    // Predicate to check if all elements in a sequence are positive (non-negative)
    spec fn positive(s: Seq<i32>) -> bool {
        forall|u: int| 0 <= u < s.len() ==> s[u] >= 0
    }

    // Method to check if all elements in an array are positive
    fn mpositive(v: &[i32]) -> (b: bool)
        ensures b == positive(v@)
    {
        for i in 0..v.len()
            invariant forall|u: int| 0 <= u < i ==> v[u] >= 0
        {
            if v[i] < 0 {
                return false;
            }
        }
        true
    }

    // Alternative implementation using boolean flag  
    fn mpositive3(v: &[i32]) -> (b: bool)
        ensures b == positive(v@)
    {
        let mut result = true;
        for i in 0..v.len()
            invariant result == (forall|u: int| 0 <= u < i ==> v[u] >= 0)
        {
            if v[i] < 0 {
                result = false;
            }
        }
        result
    }

    // Method mpositive4 (identical to mpositive3)
    fn mpositive4(v: &[i32]) -> (b: bool)
        ensures b == positive(v@)
    {
        let mut result = true;
        for i in 0..v.len()
            invariant result == (forall|u: int| 0 <= u < i ==> v[u] >= 0)
        {
            if v[i] < 0 {
                result = false;
            }
        }
        result
    }

    // Right-to-left traversal implementation - simplified
    fn mpositivertl(v: &[i32]) -> (b: bool)
        ensures b == positive(v@)
    {
        let mut i = v.len();
        /* code modified by LLM (iteration 1): fixed while loop syntax with proper braces and invariant placement */
        while i > 0
        invariant 
            0 <= i <= v.len(),
            forall|u: int| i <= u < v.len() ==> v[u] >= 0
        decreases i
        {
            i = i - 1;
            /* code modified by LLM (iteration 1): added assertion to help prove bounds before array access */
            assert(0 <= i < v.len());
            if v[i] < 0 {
                return false;
            }
        }
        /* code modified by LLM (iteration 1): added assertion to help prove postcondition when loop exits */
        assert(i == 0);
        assert(forall|u: int| 0 <= u < v.len() ==> v[u] >= 0);
        true
    }
}

fn main() {}