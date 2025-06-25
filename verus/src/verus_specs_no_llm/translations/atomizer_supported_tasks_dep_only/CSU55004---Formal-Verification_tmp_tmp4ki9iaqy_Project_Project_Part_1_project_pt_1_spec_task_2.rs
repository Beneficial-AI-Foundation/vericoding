// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn isPrefix(pre: String, str: String) -> (res: bool)
    requires
        0 < pre.len() <= str.len() //This line states that this method,
        that pre is less than || equal in length to str. Without this line, an out of bounds error is shown on line 14: "str.spec_index(i) != pre.spec_index(i)"
{
    return false;
}

}