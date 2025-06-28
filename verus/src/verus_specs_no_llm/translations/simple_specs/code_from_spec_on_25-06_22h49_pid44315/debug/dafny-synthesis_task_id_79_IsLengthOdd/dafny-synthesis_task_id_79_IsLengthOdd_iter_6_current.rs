use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsLengthOdd(s: String) -> (result: bool)
    ensures
        result <==> s@.len() % 2 == 1
{
    s.len() % 2 == 1
}

}