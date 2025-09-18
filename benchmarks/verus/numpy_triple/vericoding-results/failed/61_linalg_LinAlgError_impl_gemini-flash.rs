// <vc-preamble>
use vstd::prelude::*;

verus! {

pub enum LinAlgError {

    NonConvergence(String),

    SingularMatrix(String),

    NonSquareMatrix(String),

    IncompatibleDimensions(String),

    InvalidInput(String),

    NumericalInstability(String),

    Other(String),
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): This section remains intentionally empty as no helpers are necessary for this problem. */
// </vc-helpers>

// <vc-spec>
fn check_lin_alg_error(condition: bool, error_type: spec_fn(String) -> LinAlgError, message: String) -> (result: Option<LinAlgError>)
    ensures 
        condition == true ==> result == Some(error_type(message)),
        condition == false ==> result == None::<LinAlgError>,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The `error_type` in the function signature is a `spec_fn` which cannot be called from `exec` mode. Instead of restructuring the `error_type` parameter, the function can be directly implemented using the `error_type` spec_fn to construct the appropriate `LinAlgError` within the ensures clause. The `exec` function should now directly use the `error_type` parameter to construct `Some(error_type(message))` when `condition` is `true`. */
{
    if condition {
        Some(error_type(message))
    } else {
        None::<LinAlgError>
    }
}
// </vc-code>

}
fn main() {}