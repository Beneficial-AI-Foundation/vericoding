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
        // Since (base * height) % 2 == 0, we know base * height is even
        // We can use the property that for even numbers a: (a/2) * c == (a*c)/2
        let product = base * height;
        assert(product % 2 == 0);
        
        // For any integer division where the dividend is divisible by the divisor,
        // we have the distributive property: (a/b) * c == (a*c)/b when a % b == 0
        assert(product / 2 * length == product * length / 2) by(nonlinear_arith);
        
        // Substitute back
        assert(area * length == (base * height) / 2 * length);
        assert((base * height) / 2 * length == (base * height) * length / 2) by(nonlinear_arith);
        assert((base * height) * length == base * height * length) by(nonlinear_arith);
    }
    
    result
}

}