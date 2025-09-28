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

// </vc-helpers>

// <vc-spec>
fn check_lin_alg_error(condition: bool, error_variant: u8, message: String) -> (result: Option<LinAlgError>)
    ensures 
        condition == true ==> result.is_some(),
        condition == false ==> result == None::<LinAlgError>,
// </vc-spec>
// <vc-code>
{
    if condition {
        let error = match error_variant {
            0 => LinAlgError::NonConvergence(message),
            1 => LinAlgError::SingularMatrix(message),
            2 => LinAlgError::NonSquareMatrix(message),
            3 => LinAlgError::IncompatibleDimensions(message),
            4 => LinAlgError::InvalidInput(message),
            5 => LinAlgError::NumericalInstability(message),
            _ => LinAlgError::Other(message),
        };
        Some(error)
    } else {
        None
    }
}
// </vc-code>

}
fn main() {}