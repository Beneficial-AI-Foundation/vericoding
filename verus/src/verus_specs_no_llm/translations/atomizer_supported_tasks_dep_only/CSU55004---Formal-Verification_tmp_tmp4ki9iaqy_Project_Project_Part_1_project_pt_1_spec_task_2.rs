// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_isPrefix(pre: String, str: String) -> res:bool
    requires
        0 < pre.len() <= str.len() //This line states that this method,
        that pre is less than || equal in length to str. Without this line, an out of bounds error is shown on line 14: "str.index(i) != pre.index(i)"
;

proof fn lemma_isPrefix(pre: String, str: String) -> (res: bool)
    requires
        0 < pre.len() <= str.len() //This line states that this method,
        that pre is less than || equal in length to str. Without this line, an out of bounds error is shown on line 14: "str.index(i) != pre.index(i)"
{
    false
}

}