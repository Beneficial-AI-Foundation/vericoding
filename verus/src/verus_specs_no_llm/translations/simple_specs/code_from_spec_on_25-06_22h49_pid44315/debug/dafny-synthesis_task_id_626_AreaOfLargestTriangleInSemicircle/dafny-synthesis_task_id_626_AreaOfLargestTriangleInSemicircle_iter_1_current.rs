use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn AreaOfLargestTriangleInSemicircle(radius: int) -> (area: int)
    requires
        radius > 0
    ensures
        area == radius * radius
{
    radius * radius
}

}

The implementation is straightforward - since the postcondition requires that `area == radius * radius`, and we know from the mathematical properties of the largest triangle inscribed in a semicircle that this is indeed the correct formula, we simply return `radius * radius`. 

The verification succeeds because: