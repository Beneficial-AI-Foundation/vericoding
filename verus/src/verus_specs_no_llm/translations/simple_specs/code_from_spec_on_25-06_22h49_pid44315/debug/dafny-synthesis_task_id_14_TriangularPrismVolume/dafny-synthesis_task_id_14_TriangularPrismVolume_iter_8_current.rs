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
    
    // Use nonlinear arithmetic to prove the mathematical equivalence directly
    assert(result == (base * height * length) / 2) by(nonlinear_arith)
        requires 
            base > 0,
            height > 0, 
            length > 0,
            (base * height) % 2 == 0,
            area == (base * height) / 2,
            result == area * length;
    
    result
}

}