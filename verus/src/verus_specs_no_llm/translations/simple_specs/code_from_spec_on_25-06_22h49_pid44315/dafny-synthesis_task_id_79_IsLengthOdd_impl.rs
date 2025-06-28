use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn IsLengthOdd(s: &str) -> (result: bool)
    ensures
        result <==> s@.len() % 2 == 1
{
    let len = s.len();
    len % 2 == 1
}

}