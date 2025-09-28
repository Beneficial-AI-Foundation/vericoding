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
/* helper modified by LLM (iteration 4): fixed wildcard arm to avoid string concatenation and use provided message */
fn variant_to_error(variant: u8, message: String) -> LinAlgError {
    match variant % 7 {
        0 => LinAlgError::NonConvergence(message),
        1 => LinAlgError::SingularMatrix(message),
        2 => LinAlgError::NonSquareMatrix(message),
        3 => LinAlgError::IncompatibleDimensions(message),
        4 => LinAlgError::InvalidInput(message),
        5 => LinAlgError::NumericalInstability(message),
        6 => LinAlgError::Other(message),
        _ => LinAlgError::Other(message),
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
{
    /* code modified by LLM (iteration 4): code remains correct */
    if condition {
        let error = variant_to_error(error_variant, message);
        Some(error)
    } else {
        None
    }
}
// </vc-code>

}
fn main() {}