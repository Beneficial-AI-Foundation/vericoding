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
        0
    }

    // Main function for demonstration
    fn Main() 
    {
        // Call F to demonstrate
        let result = F();
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
        
        // Show that m == p + (q - p) / 2
        assert(m == (p + q) / 2 == (2 * p + q - p) / 2 == p + (q - p) / 2);
        
        // Show p <= m <= q
        assert(2 * p <= p + q <= 2 * q);
        assert(p <= (p + q) / 2 <= q);
        
        // Show m - p <= q - m
        assert(m - p == (p + q) / 2 - p == (q - p) / 2);
        assert(q - m == q - (p + q) / 2 == (2 * q - p - q) / 2 == (q - p) / 2);
        assert(m - p == (q - p) / 2 == q - m);
        
        // Show 0 <= (q - m) - (m - p) <= 1
        assert((q - m) - (m - p) == (q - p) / 2 - (q - p) / 2 == 0);
        assert(0 <= 0 <= 1);
    }
}

fn main() {}