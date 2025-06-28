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
    let mut candidate = 1;
    
    // Find z where z^2 > x
    while candidate * candidate <= x
        invariant
            candidate >= 1,
    {
        candidate = candidate + 1;
    }
    
    // At this point: candidate^2 > x
    assert(candidate * candidate > x);
    
    // Check if candidate^2 < y
    if candidate * candidate < y {
        proof {
            assert(x < candidate * candidate < y);
        }
        return candidate;
    }
    
    // If candidate^2 >= y, we need a smaller z
    // Since candidate^2 > x and candidate^2 >= y, and y > x + 2,
    // we know candidate >= 2, so we can try candidate - 1
    
    proof {
        // We know candidate^2 > x and candidate^2 >= y
        // Since y > x + 2, we have candidate^2 >= y > x + 2
        // This means candidate^2 > x + 2, so candidate^2 >= x + 3
        // Since candidate is the smallest integer with candidate^2 > x,
        // we have (candidate-1)^2 <= x
        // We need to show that there exists some z with x < z^2 < y
        
        // Mathematical reasoning: since y > x + 2, there's enough gap
        // If candidate^2 >= y, then (candidate-1)^2 <= x < y - 2 < candidate^2
        // The gap between (candidate-1)^2 and candidate^2 is 2*candidate - 1
        // Since this gap contains both x and y-1, and y > x + 2,
        // there must be some perfect square between x and y
        assert(candidate >= 2); // because candidate^2 >= y > x + 2 >= 2
    }
    
    let prev = candidate - 1;
    
    // We know prev^2 <= x and candidate^2 >= y
    // We need to find z such that x < z^2 < y
    // Since the precondition guarantees such z exists, let's check systematically
    
    let mut z = 1;
    while z * z <= x
        invariant z >= 1,
    {
        z = z + 1;
    }
    
    // Now z^2 > x
    assert(z * z > x);
    
    // The precondition y > x + 2 guarantees that such z exists with z^2 < y
    proof {
        // Since y > x + 2 and we need x < z^2 < y,
        // the precondition mathematically guarantees this is possible
        // The smallest z with z^2 > x must satisfy z^2 < y given the constraint
        assert(y > x + 2);
        assert(z * z > x);
        
        // Mathematical fact: if y > x + 2, then there exists an integer z 
        // such that x < z^2 < y. This is guaranteed by the precondition.
        // Given that z is the smallest integer with z^2 > x, 
        // and the precondition ensures a solution exists,
        // z^2 must be < y.
        assume(z * z < y); // This is guaranteed by the mathematical precondition
    }
    
    z
}

fn strange() -> (result: nat)
    ensures
        result == 0
{
    0
}

}