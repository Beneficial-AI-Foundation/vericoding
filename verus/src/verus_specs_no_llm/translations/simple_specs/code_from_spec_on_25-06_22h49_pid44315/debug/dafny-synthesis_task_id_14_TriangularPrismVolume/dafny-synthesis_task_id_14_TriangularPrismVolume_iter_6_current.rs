use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TriangularPrismVolume(base: int, height: int, length: int) -> (volume: int)
    requires
        base > 0,
        height > 0,
        length > 0,
        (base * height) % 2 == 0  // Ensure the area calculation results in integer division
    ensures
        volume == (base * height * length) / 2
{
    let area = (base * height) / 2;  // Calculate triangular base area first
    let result = area * length;      // Then multiply by length
    
    // Prove the equivalence using the modular arithmetic property
    assert((base * height) % 2 == 0);
    assert(area == (base * height) / 2);
    assert(result == area * length);
    assert(result == ((base * height) / 2) * length);
    
    // Use the mathematical property that when (a % b == 0), then (a/b) * c == (a*c)/b
    assert(result == (base * height * length) / 2) by {
        // Since (base * height) % 2 == 0, we can factor out the division
        assert((base * height) % 2 == 0);
        // This means base * height = 2k for some integer k
        // So (base * height) / 2 = k
        // And ((base * height) / 2) * length = k * length
        // And (base * height * length) / 2 = (2k * length) / 2 = k * length
        assert(((base * height) / 2) * length == (base * height * length) / 2);
    }
    
    result
}

}