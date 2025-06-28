use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ElementAtIndexAfterRotation(l: Seq<int>, n: int, index: int) -> (element: int)
    requires
        n >= 0,
        0 <= index < l.len(),
        l.len() > 0
    ensures
        element == l.spec_index((index - n + l.len()) % l.len())
{
    let len = l.len();
    
    // Calculate the original index properly handling negative results
    let temp = index - n + len;
    let original_index = temp % len;
    
    // Use spec_index for Seq access
    l.spec_index(original_index)
}

}