use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TriangularPrismVolume(base: int, height: int, length: int) -> (volume: int)
    requires
        base > 0,
        height > 0,
        length > 0
    ensures
        volume == (base * height * length) / 2
{
    let product = base * height * length;
    let result = product / 2;
    
    // The division operation in Verus for integers should work directly
    // The postcondition matches exactly what we're computing
    result
}

}