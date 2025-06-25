//This method should return true iff pre is a prefix of str. That is, str starts with pre
// SPEC 
//This method should return true iff pre is a prefix of str. That is, str starts with pre
pub fn isPrefix(pre: &str, str: &str) -> bool
    requires(0 < pre.len() <= str.len()) //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
}


//This method should return true iff sub is a substring of str. That is, str contains sub
// SPEC 

//This method should return true iff sub is a substring of str. That is, str contains sub
pub fn isSubstring(sub: &str, str: &str) -> bool
    requires(0 < sub.len() <= str.len()) //This method requires that sub is less than or equal in length to str
{
}


//This method should return true iff str1 and str1 have a common substring of length k
// SPEC 

//This method should return true iff str1 and str1 have a common substring of length k
pub fn haveCommonKSubstring(k: nat, str1: &str, str2: &str) -> bool
    requires(0 < k <= str1.len() && 0 < k <= str2.len()) //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
{
}


//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
// SPEC 

//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
pub fn maxCommonSubstringLength(str1: &str, str2: &str) -> nat
    requires(0 < str1.len() && 0 < str1.len())
{
}


//Main to test each method
//ATOM_PLACEHOLDER_Main