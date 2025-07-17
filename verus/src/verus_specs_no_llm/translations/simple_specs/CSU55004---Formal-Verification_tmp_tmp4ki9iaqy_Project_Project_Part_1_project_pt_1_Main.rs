// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_isPrefix(pre: String, str: String) -> res:bool)
  requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
  res := false;
  return res;
}


//ATOM

//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
method maxCommonSubstringLength(str1:string, str2:string) returns(len:nat)
  requires 0 < |str1| && 0 < |str1|
{
  len := 0;
  return len;
}


//ATOM

//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool
    requires
        0 < pre.len() <= str.len() //This line states that this method,
        that pre is less than || equal in length to str. Without this line, an out of bounds error is shown on line 14: "str.index(i) != pre.index(i)",
        0 < str1.len() && 0 < str1.len(),
        0 < sub.len() <= str.len() //This method,
        that sub is less than || equal in length to str
;

proof fn lemma_isPrefix(pre: String, str: String) -> (res: bool)
  requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
  res := false;
  return res;
}


//ATOM

//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
method maxCommonSubstringLength(str1:string, str2: string) returns(len:nat)
  requires 0 < |str1| && 0 < |str1|
{
  len := 0;
  return len;
}


//ATOM

//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub: String, str: string) returns(res:bool)
    requires
        0 < pre.len() <= str.len() //This line states that this method,
        that pre is less than || equal in length to str. Without this line, an out of bounds error is shown on line 14: "str.index(i) != pre.index(i)",
        0 < str1.len() && 0 < str1.len(),
        0 < sub.len() <= str.len() //This method,
        that sub is less than || equal in length to str
{
    (0, 0, 0, String::new(), 0)
}

}