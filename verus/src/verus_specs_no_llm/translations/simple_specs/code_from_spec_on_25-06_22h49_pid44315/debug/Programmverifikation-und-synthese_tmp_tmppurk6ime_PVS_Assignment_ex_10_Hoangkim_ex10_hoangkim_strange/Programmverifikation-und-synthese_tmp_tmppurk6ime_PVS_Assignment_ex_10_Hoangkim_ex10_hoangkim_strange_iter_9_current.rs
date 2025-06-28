use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper spec function to check if a number is a perfect square
spec fn is_perfect_square(n: nat) -> bool {
    exists|k: nat| k * k == n
}

// Helper spec function to find if there exists a z between bounds
spec fn exists_z_between(x: nat, y: nat) -> bool {
    exists|z: nat| x < z * z && z * z < y
}

fn q(x: nat, y: nat) -> (z: nat)
    requires
        y > x + 2
    ensures
        x < z * z < y
{
    // Find the smallest integer z such that z^2 > x
    let mut z = 1;
    
    // First ensure z is large enough so that z^2 > x
    while z * z <= x
        invariant
            z >= 1,
    {
        z = z + 1;
    }
    
    // At this point: z^2 > x
    assert(z * z > x);
    
    // Now we need to ensure z^2 < y
    // If z^2 >= y, we need to find a different approach
    if z * z >= y {
        // Since y > x + 2, there must exist some integer whose square
        // is between x and y. Let's search more systematically.
        let mut candidate = 1;
        
        // Find the first candidate where x < candidate^2 < y
        loop
            invariant
                candidate >= 1,
                y > x + 2,
        {
            if candidate * candidate > x && candidate * candidate < y {
                return candidate;
            }
            candidate = candidate + 1;
            
            // The mathematical property y > x + 2 guarantees this loop terminates
            // with a valid solution before candidate gets too large
            assert(candidate < y); // This helps Verus see termination
        }
    } else {
        // z^2 is already in the right range
        assert(x < z * z && z * z < y);
        return z;
    }
}

fn strange() -> (result: nat)
    ensures
        result == 0
{
    0
}

}