/* 
{
  "name": "numpy.where",
  "category": "Searching",
  "description": "Return elements chosen from x or y depending on condition",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.where.html",
  "doc": "Return elements chosen from `x` or `y` depending on `condition`.\n\nNote\n----\nWhen only `condition` is provided, this function is a shorthand for\n``np.asarray(condition).nonzero()``. Using `nonzero` directly should be\npreferred, as it behaves correctly for subclasses. The rest of this\ndocumentation covers only the case where all three arguments are\nprovided.\n\nParameters\n----------\ncondition : array_like, bool\n    Where True, yield `x`, otherwise yield `y`.\nx, y : array_like\n    Values from which to choose. `x`, `y` and `condition` need to be\n    broadcastable to some shape.\n\nReturns\n-------\nout : ndarray\n    An array with elements from `x` where `condition` is True, and elements\n    from `y` elsewhere.\n\nSee Also\n--------\nchoose\nnonzero : The function that is called when x and y are omitted",
}
*/

/* Return elements chosen from x or y depending on condition.
   For each position i, if condition[i] is True, take x[i], otherwise take y[i]. */

/* Specification: numpy_where returns an array where elements are chosen from x when condition is True,
   and from y when condition is False. */
use vstd::prelude::*;

verus! {
// <vc-helpers>
// </vc-helpers>
fn numpy_where(condition: Vec<bool>, x: Vec<f64>, y: Vec<f64>) -> (result: Vec<f64>)
    requires
        condition.len() == x.len(),
        x.len() == y.len(),
    ensures
        result.len() == condition.len(),
        forall|i: int| 0 <= i < condition.len() ==> {
            if condition[i] {
                result[i] == x[i]
            } else {
                result[i] == y[i]
            }
        },
// <vc-implementation>
    {
        assume(false);
        return Vec::new(); // TODO: Remove this line and implement the function body
    }
// </vc-implementation>
proof fn numpy_where_spec(condition: Vec<bool>, x: Vec<f64>, y: Vec<f64>)
    requires
        condition.len() == x.len(),
        x.len() == y.len(),
// <vc-proof>
    {
        assume(false); // TODO: Remove this line and implement the proof
    }
// </vc-proof>

fn main() {
}

}