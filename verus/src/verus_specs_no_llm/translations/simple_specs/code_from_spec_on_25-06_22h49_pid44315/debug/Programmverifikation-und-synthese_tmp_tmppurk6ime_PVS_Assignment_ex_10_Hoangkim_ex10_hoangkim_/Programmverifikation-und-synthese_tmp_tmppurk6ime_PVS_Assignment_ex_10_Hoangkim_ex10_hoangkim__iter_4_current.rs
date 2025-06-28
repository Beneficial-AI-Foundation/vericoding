use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn q(x: nat, y: nat) -> (z: nat)
    requires y > x + 2
    ensures x < z * z < y
{
    // We need to find z such that x < z^2 < y
    // Given y > x + 2, we have enough space to find such z
    
    if x == 0 {
        // If x = 0, then y >= 3 (since y > 0 + 2)
        // We need 0 < z^2 < y
        // z = 1 works: 0 < 1 < y (since y >= 3)
        1
    } else if x == 1 {
        // If x = 1, then y >= 4 (since y > 1 + 2)
        // We need 1 < z^2 < y
        // z = 2 gives z^2 = 4, but we need 4 < y
        // Since y >= 4, we need y > 4, so y >= 5
        // But our precondition only guarantees y >= 4
        // However, since y > x + 2 = 3, we have y >= 4
        // Let's try z = 1, but 1^2 = 1, so 1 < 1 is false
        // We need a stronger approach
        
        // Actually, if y > x + 2 and x = 1, then y > 3, so y >= 4
        // But we need something between 1 and y
        // If y = 4, there's no integer z where 1 < z^2 < 4
        // This suggests we might need y > x + 3 for this to work
        
        // For now, let's assume y >= 5 when x = 1
        assert(y > 3);  // From precondition
        if y > 4 {
            2  // 1 < 4 < y when y > 4
        } else {
            // y = 4, need 1 < z^2 < 4, impossible with integers
            // This case violates the postcondition, so it's unreachable
            // with a satisfiable specification
            1  // This will fail verification, indicating the spec issue
        }
    } else if x == 2 {
        // If x = 2, then y >= 5 (since y > 2 + 2)
        // We need 2 < z^2 < y
        // z = 2 gives z^2 = 4, and 2 < 4, so we need 4 < y
        // Since y >= 5, we have 4 < y, so z = 2 works
        2
    } else if x == 3 {
        // If x = 3, then y >= 6
        // We need 3 < z^2 < y
        // z = 2 gives z^2 = 4, and 3 < 4 < 6, so z = 2 works
        2
    } else {
        // For larger x, we can often use z = x - 1 or find appropriate z
        // Let's try z such that z^2 is close to x + 1
        
        // Try z where z^2 ≈ x + 1
        let z_candidate = x; // Start with x as candidate
        
        if x < z_candidate * z_candidate && z_candidate * z_candidate < y {
            z_candidate
        } else {
            // Try z = x - 1
            let z_alt = if x > 0 { x - 1 } else { 1 };
            if x < z_alt * z_alt && z_alt * z_alt < y {
                z_alt
            } else {
                // Find the right z by trying a few values
                // Since we have y > x + 2, there should be room
                if x < 1 * 1 && 1 * 1 < y { 1 }
                else if x < 2 * 2 && 2 * 2 < y { 2 }
                else if x < 3 * 3 && 3 * 3 < y { 3 }
                else { 1 } // fallback, may not verify
            }
        }
    }
}

method strange()
    ensures 1 == 2
{
    // This method has an impossible postcondition
    // In Verus, we can indicate this is unreachable/impossible
    assert(false);
}

}