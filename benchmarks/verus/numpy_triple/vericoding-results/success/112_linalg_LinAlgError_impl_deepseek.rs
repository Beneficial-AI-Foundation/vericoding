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
/* helper modified by LLM (iteration 5): Fix function signature to use proper return value */
fn get_lin_alg_error(error_variant: u8, message: String) -> (result: LinAlgError)
    ensures
        (error_variant == 0) ==> result == LinAlgError::NonConvergence(message),
        (error_variant == 1) ==> result == LinAlgError::SingularMatrix(message),
        (error_variant == 2) ==> result == LinAlgError::NonSquareMatrix(message),
        (error_variant == 3) ==> result == LinAlgError::IncompatibleDimensions(message),
        (error_variant == 4) ==> result == LinAlgError::InvalidInput(message),
        (error_variant == 5) ==> result == LinAlgError::NumericalInstability(message),
        (error_variant >= 6) ==> result == LinAlgError::Other(message),
{
    if error_variant == 0 {
        LinAlgError::NonConvergence(message)
    } else if error_variant == 1 {
        LinAlgError::SingularMatrix(message)
    } else if error_variant == 2 {
        LinAlgError::NonSquareMatrix(message)
    } else if error_variant == 3 {
        LinAlgError::IncompatibleDimensions(message)
    } else if error_variant == 4 {
        LinAlgError::InvalidInput(message)
    } else if error_variant == 5 {
        LinAlgError::NumericalInstability(message)
    } else {
        LinAlgError::Other(message)
    }
}
// </vc-helpers>

// <vc-spec>
fn check_lin_alg_error(condition: bool, error_variant: u8, message: String) -> (result: Option<LinAlgError>)
    ensures 
        condition == true ==> result.is_some(),
        condition == false ==> result == None::<LinAlgError>,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed result variable usage */
{
    if !condition {
        None
    } else {
        let result = get_lin_alg_error(error_variant, message);
        Some(result)
    }
}
// </vc-code>

}
fn main() {}