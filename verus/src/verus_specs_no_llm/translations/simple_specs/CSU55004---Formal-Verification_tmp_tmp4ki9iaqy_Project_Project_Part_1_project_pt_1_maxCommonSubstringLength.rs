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
  requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
  res := false;
  return res;
}


//ATOM

//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub: String, str: string) returns(res:bool)
    requires
        0 < pre.len() <= str.len() //This line states that this method,
        that pre is less than || equal in length to str. Without this line, an out of bounds error is shown on line 14: "str.spec_index(i) != pre.spec_index(i)",
        0 < sub.len() <= str.len() //This method,
        that sub is less than || equal in length to str
{
    return (0, 0, String::new(), 0);
}

}