use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn SquarePyramidSurfaceArea(baseEdge: int, height: int) -> (area: int)
    requires
        baseEdge > 0,
        height > 0
    ensures
        area == baseEdge * baseEdge + 2 * baseEdge * height
{
    let base_area = baseEdge * baseEdge;
    let partial_faces_area = 2 * baseEdge * height;
    let area = base_area + partial_faces_area;
    
    // Add proof assertion to help verification
    assert(area == baseEdge * baseEdge + 2 * baseEdge * height);
    
    area
}

}