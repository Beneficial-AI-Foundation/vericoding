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
/* helper modified by LLM (iteration 5): provide spec constructors for all LinAlgError variants to be used as error_type arguments */
spec fn mk_non_convergence(message: String) -> LinAlgError { LinAlgError::NonConvergence(message) }
spec fn mk_singular_matrix(message: String) -> LinAlgError { LinAlgError::SingularMatrix(message) }
spec fn mk_non_square_matrix(message: String) -> LinAlgError { LinAlgError::NonSquareMatrix(message) }
spec fn mk_incompatible_dimensions(message: String) -> LinAlgError { LinAlgError::IncompatibleDimensions(message) }
spec fn mk_invalid_input(message: String) -> LinAlgError { LinAlgError::InvalidInput(message) }
spec fn mk_numerical_instability(message: String) -> LinAlgError { LinAlgError::NumericalInstability(message) }
spec fn mk_other(message: String) -> LinAlgError { LinAlgError::Other(message) }
// </vc-helpers>

// <vc-spec>
fn check_lin_alg_error(condition: bool, error_type: spec_fn(String) -> LinAlgError, message: String) -> (result: Option<LinAlgError>)
    ensures 
        condition == true ==> result == Some(error_type(message)),
        condition == false ==> result == None::<LinAlgError>,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): return exactly the error produced by the provided spec function when condition is true */
    if condition {
        let e = error_type(message);
        Some(e)
    } else {
        None::<LinAlgError>
    }
}
// </vc-code>

}
fn main() {}