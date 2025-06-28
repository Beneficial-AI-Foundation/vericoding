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
    
    // Prove the equivalence
    assert((base * height) % 2 == 0);
    assert(area == (base * height) / 2);
    assert(result == area * length);
    assert(result == ((base * height) / 2) * length);
    assert(result == (base * height * length) / 2) by {
        // Mathematical property: (a/b) * c == (a*c)/b when a % b == 0
        assert((base * height) % 2 == 0);
        assert(((base * height) / 2) * length == (base * height * length) / 2);
    }
    
    result
}

}