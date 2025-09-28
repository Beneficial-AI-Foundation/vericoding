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
/* helper modified by LLM (iteration 3): prove get_element equals underlying fields */
fn lemma_broadcast_res(res: &BroadcastObject)
    requires
        res.well_formed(),
    ensures
        forall|i: int, j: int|
            0 <= i < res.shape.0 && 0 <= j < res.shape.1 ==>
            res.get_element(i, j) == (res.x_data[i], res.y_data[j]),
{
    proof {
        assert(forall|i: int, j: int| 0 <= i < res.shape.0 && 0 <= j < res.shape.1 ==>
            res.get_element(i, j) == (res.x_data[i], res.y_data[j]));
    }
}

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
/* code modified by LLM (iteration 3): compute lengths before moving vectors and construct BroadcastObject */
{
    let x_len = x.len();
    let y_len = y.len();
    let res = BroadcastObject { x_data: x, y_data: y, shape: (x_len, y_len) };
    lemma_broadcast_res(&res);
    res
}

// </vc-code>

}
fn main() {}