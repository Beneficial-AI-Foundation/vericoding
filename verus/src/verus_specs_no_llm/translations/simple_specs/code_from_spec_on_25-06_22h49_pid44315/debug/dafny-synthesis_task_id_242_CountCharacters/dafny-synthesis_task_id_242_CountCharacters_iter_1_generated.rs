use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountCharacters(s: String) -> (count: int)
    ensures
        count >= 0,
        count == s.len()
{
    s.len() as int
}

}