//This method should return true iff pre is a prefix of str. That is, str starts with pre
// SPEC 
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
}


//This method should return true iff sub is a substring of str. That is, str contains sub
// SPEC 

//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
{
}


//This method should return true iff str1 and str1 have a common substring of length k
//ATOM_PLACEHOLDER_haveCommonKSubstring

//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
//ATOM_PLACEHOLDER_maxCommonSubstringLength

//Main to test each method
//ATOM_PLACEHOLDER_Main



