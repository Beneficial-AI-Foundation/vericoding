// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn isPrefix(pre: String, str: String) -> (res: bool)
    requires 0 < pre.len() <= str.len() //This line states that this method,
             that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
}

}