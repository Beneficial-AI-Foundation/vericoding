use vstd::prelude::*;

verus! {
    // Specification function for min
    spec fn min(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    // Proof function to establish properties of min
    proof fn min_properties(a: int, b: int)
        ensures 
            min(a, b) <= a && min(a, b) <= b,
            min(a, b) == a || min(a, b) == b,
    {
        // The properties follow directly from the definition of min
        // If a < b, then min(a, b) == a, so min(a, b) <= a and min(a, b) <= b (since a < b)
        // If a >= b, then min(a, b) == b, so min(a, b) <= a (since b <= a) and min(a, b) <= b
    }

    // Executable method for min with concrete types
    fn minMethod(a: i32, b: i32) -> (c: i32)
        ensures 
            c <= a && c <= b,
            c == a || c == b,
            c == min(a as int, b as int),
    {
        if a < b {
            a
        } else {
            b
        }
    }

    // Ghost function (spec function in Verus)
    spec fn minFunction(a: int, b: int) -> int {
        if a < b { a } else { b }
    }

    // Proof function to establish properties of minFunction
    proof fn minFunction_properties(a: int, b: int)
        ensures 
            minFunction(a, b) <= a && minFunction(a, b) <= b,
            minFunction(a, b) == a || minFunction(a, b) == b,
    {
        // Same reasoning as min_properties since minFunction has identical definition to min
    }

    // Method to find minimum in array
    fn minArray(a: &[i32]) -> (m: i32)
        requires a.len() > 0
        ensures 
            forall|k: int| 0 <= k < a.len() ==> m <= a[k],
            exists|k: int| 0 <= k < a.len() && m == a[k],
    {
        let mut min_val = a[0];
        let mut i = 1;
        
        while i < a.len()
            invariant 
                0 < i <= a.len(),
                forall|k: int| 0 <= k < i ==> min_val <= a[k],
                exists|k: int| 0 <= k < i && min_val == a[k],
        {
            if a[i] < min_val {
                min_val = a[i];
            }
            i += 1;
        }
        
        min_val
    }

    fn main() {
        let x = minMethod(5, 3);
        assert(x == 3);
        
        let arr = [1, 5, 2, 8, 3];
        let min_elem = minArray(&arr);
        assert(min_elem == 1);
    }
}