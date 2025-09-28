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
        match error_variant {
            0 => Some(LinAlgError::NonConvergence(message)),
            1 => Some(LinAlgError::SingularMatrix(message)),
            2 => Some(LinAlgError::NonSquareMatrix(message)),
            3 => Some(LinAlgError::IncompatibleDimensions(message)),
            4 => Some(LinAlgError::InvalidInput(message)),
            5 => Some(LinAlgError::NumericalInstability(message)),
            _ => Some(LinAlgError::Other(message)),
        }
    } else {
        None
    }
}
// </vc-code>

}
fn main() {}