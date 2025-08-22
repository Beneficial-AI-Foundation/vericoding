use vstd::prelude::*;

verus! {
    // Spec function for F
    spec fn F_spec() -> int {
        0
    }

    // Executable function for F
    fn F() -> (r: i32)
        ensures r == F_spec() && r <= 0
    {
    return 0;  // TODO: Remove this line and implement the function body
    }

    // Main function for demonstration
    fn Main() 
    {
    // TODO: Remove this comment and implement the function body
    }

    // Spec function for Mid using mathematical integers
    spec fn Mid_spec(p: int, q: int) -> int 
        recommends p <= q
    {
        (p + q) / 2
    }

    // Proof function to verify the properties of Mid
    proof fn Mid_properties(p: int, q: int)
        requires p <= q
        ensures 
            p <= Mid_spec(p, q) <= q,
            Mid_spec(p, q) - p <= q - Mid_spec(p, q),
            0 <= (q - Mid_spec(p, q)) - (Mid_spec(p, q) - p) <= 1,
            Mid_spec(p, q) == p + (q - p) / 2
    {
        let m = Mid_spec(p, q);
        assert(m == (p + q) / 2);
        assert(m == p + (q - p) / 2);
        
        // The properties follow from integer arithmetic
        assert(p <= m <= q);
        assert(m - p <= q - m);
        assert(0 <= (q - m) - (m - p) <= 1);
    }
}

fn main() {}