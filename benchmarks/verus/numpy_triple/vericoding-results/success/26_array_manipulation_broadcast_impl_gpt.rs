// <vc-preamble>
use vstd::prelude::*;

verus! {

struct BroadcastObject {

    x_data: Vec<f32>,

    y_data: Vec<f32>,

    shape: (usize, usize),
}

impl BroadcastObject {
    spec fn well_formed(&self) -> bool {
        self.shape.0 == self.x_data.len() &&
        self.shape.1 == self.y_data.len()
    }

    spec fn get_element(&self, i: int, j: int) -> (f32, f32)
        recommends 
            self.well_formed(),
            0 <= i < self.shape.0,
            0 <= j < self.shape.1,
    {
        (self.x_data[i], self.y_data[j])
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn broadcast(x: Vec<f32>, y: Vec<f32>) -> (result: BroadcastObject)
    requires 
        x.len() > 0,
        y.len() > 0,
    ensures
        result.well_formed(),
        result.shape == (x.len(), y.len()),
        forall|i: int, j: int| 
            0 <= i < x.len() && 0 <= j < y.len() ==> 
            result.get_element(i, j) == (x[i], y[j])
// </vc-spec>
// <vc-code>
{
    let s0 = x.len();
    let s1 = y.len();
    let result = BroadcastObject { x_data: x, y_data: y, shape: (s0, s1) };
    result
}
// </vc-code>

}
fn main() {}