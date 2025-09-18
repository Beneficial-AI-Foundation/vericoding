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
/* helper modified by LLM (iteration 5): identity spec helper for spec constructors */
spec fn call_error_ctor(f: spec_fn(String) -> LinAlgError, s: String) -> LinAlgError { f(s) }
// </vc-helpers>

// <vc-spec>
fn check_lin_alg_error(condition: bool, error_type: spec_fn(String) -> LinAlgError, message: String) -> (result: Option<LinAlgError>)
    ensures 
        condition == true ==> result == Some(error_type(message)),
        condition == false ==> result == None::<LinAlgError>,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): call spec constructor to produce matching error when condition is true */
    if condition {
        Some(error_type(message))
    } else {
        None::<LinAlgError>
    }
}
// </vc-code>

}
fn main() {}