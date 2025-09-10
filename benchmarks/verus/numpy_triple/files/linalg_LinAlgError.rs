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

fn check_lin_alg_error(condition: bool, error_type: spec_fn(String) -> LinAlgError, message: String) -> (result: Option<LinAlgError>)
    ensures 
        condition == true ==> result == Some(error_type(message)),
        condition == false ==> result == None::<LinAlgError>,
{
    assume(false);
    unreached();
}

}
fn main() {}