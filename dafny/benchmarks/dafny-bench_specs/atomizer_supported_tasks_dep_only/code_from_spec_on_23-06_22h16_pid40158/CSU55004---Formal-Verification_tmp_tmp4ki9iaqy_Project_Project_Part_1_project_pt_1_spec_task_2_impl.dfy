//IMPL isPrefix
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
    ensures res == (forall j :: 0 <= j < |pre| ==> str[j] == pre[j])
{
    var i := 0;
    /* code modified by LLM (iteration 4): initialized res to true at start */
    res := true;
    while i < |pre|
        invariant 0 <= i <= |pre|
        /* code modified by LLM (iteration 4): maintain that all characters up to i match */
        invariant forall j :: 0 <= j < i ==> str[j] == pre[j]
        /* code modified by LLM (iteration 4): maintain res reflects whether we've found a mismatch */
        invariant res == (forall j :: 0 <= j < i ==> str[j] == pre[j])
    {
        if str[i] != pre[i] {
            res := false;
            return;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 4): assert postcondition establishment */
    assert i == |pre|;
    assert forall j :: 0 <= j < |pre| ==> str[j] == pre[j];
}

//IMPL isSubstring
//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
    ensures res == (exists i :: 0 <= i <= |str| - |sub| && forall j :: 0 <= j < |sub| ==> str[i + j] == sub[j])
{
    var i := 0;
    /* code modified by LLM (iteration 4): initialized res to false */
    res := false;
    while i <= |str| - |sub|
        invariant 0 <= i <= |str| - |sub| + 1
        /* code modified by LLM (iteration 4): simplified invariant - if res is true, we found a match */
        invariant res ==> exists k :: 0 <= k < i && forall j :: 0 <= j < |sub| ==> str[k + j] == sub[j]
        /* code modified by LLM (iteration 4): if res is false, no match found in positions checked so far */
        invariant !res ==> forall k :: 0 <= k < i ==> exists j :: 0 <= j < |sub| && str[k + j] != sub[j]
    {
        /* code modified by LLM (iteration 4): check if substring matches at position i */
        var isMatch := true;
        var j := 0;
        while j < |sub| && isMatch
            invariant 0 <= j <= |sub|
            invariant isMatch ==> forall k :: 0 <= k < j ==> str[i + k] == sub[k]
            invariant !isMatch ==> exists k :: 0 <= k < j && str[i + k] != sub[k]
        {
            if str[i + j] != sub[j] {
                isMatch := false;
            }
            j := j + 1;
        }
        
        if isMatch {
            /* code modified by LLM (iteration 4): we found a complete match */
            assert forall k :: 0 <= k < |sub| ==> str[i + k] == sub[k];
            res := true;
            return;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 4): loop completed without finding match */
    assert forall k :: 0 <= k <= |str| - |sub| ==> exists j :: 0 <= j < |sub| && str[k + j] != sub[j];
}

//ATOM haveCommonKSubstring
//This method should return true iff str1 and str1 have a common substring of length k
//ATOM_PLACEHOLDER_haveCommonKSubstring

//ATOM maxCommonSubstringLength
//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
//ATOM_PLACEHOLDER_maxCommonSubstringLength

//ATOM Main
//Main to test each method
//ATOM_PLACEHOLDER_Main