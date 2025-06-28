use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn dog_years(human_years: int) -> (result: int)
    requires
        human_years >= 0,
    ensures
        result == 7 * human_years,
{
    7 * human_years
}

}