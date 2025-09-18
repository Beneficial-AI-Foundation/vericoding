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
/* helper modified by LLM (iteration 5): Fix function signature in helper section */
fn check_lin_alg_error(condition: bool, error_type: spec_fn(String) -> LinAlgError, message: String) -> (result: Option<LinAlgError>)
    ensures 
        condition == true ==> result == Some(error_type(message)),
        condition == false ==> result == None::<LinAlgError>,
// </vc-helpers>

// <vc-spec>
fn check_lin_alg_error(condition: bool, error_type: spec_fn(String) -> LinAlgError, message: String) -> (result: Option<LinAlgError>)
    ensures 
        condition == true ==> result == Some(error_type(message)),
        condition == false ==> result == None::<LinAlgError>,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Match helper function signature */
{
    if condition {
        let error = error_type(message);
        Some(error)
    } else {
        None
    }
}
// </vc-code>

}
fn main() {}