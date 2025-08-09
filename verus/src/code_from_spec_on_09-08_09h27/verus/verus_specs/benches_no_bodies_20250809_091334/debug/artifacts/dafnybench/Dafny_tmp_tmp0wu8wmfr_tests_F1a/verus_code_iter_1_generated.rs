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
        // The properties follow from the mathematical properties of integer division
        // Let's prove each property step by step
        
        // First, let's establish that (p + q) / 2 == p + (q - p) / 2
        assert((p + q) / 2 == p + (q - p) / 2) by {
            assert(p + q == p + p + (q - p));
            assert(p + q == 2 * p + (q - p));
            assert((p + q) / 2 == (2 * p + (q - p)) / 2);
            assert((2 * p + (q - p)) / 2 == p + (q - p) / 2);
        };
        
        let mid = Mid_spec(p, q);
        let half_diff = (q - p) / 2;
        
        // Since p <= q, we have q - p >= 0, so (q - p) / 2 >= 0
        // Therefore mid = p + (q - p) / 2 >= p
        assert(p <= mid);
        
        // We need to show mid <= q
        // Since (q - p) / 2 <= q - p (integer division property)
        // We have mid = p + (q - p) / 2 <= p + (q - p) = q
        assert(mid <= q);
        
        // For the second property: Mid_spec(p, q) - p <= q - Mid_spec(p, q)
        // This is equivalent to: 2 * Mid_spec(p, q) <= p + q
        // Since Mid_spec(p, q) = (p + q) / 2, and (p + q) / 2 <= (p + q) / 2 is always true
        // We need: 2 * ((p + q) / 2) <= p + q
        // By integer division properties, this is always true
        assert(mid - p <= q - mid);
        
        // For the third property: 0 <= (q - mid) - (mid - p) <= 1
        // This simplifies to: 0 <= q + p - 2 * mid <= 1
        // Since mid = (p + q) / 2, we have: q + p - 2 * mid = (p + q) - 2 * ((p + q) / 2)
        // By properties of integer division, this is either 0 or 1
        let diff = (q - mid) - (mid - p);
        assert(diff == p + q - 2 * mid);
        assert(0 <= diff <= 1);
    }
}

fn main() {}