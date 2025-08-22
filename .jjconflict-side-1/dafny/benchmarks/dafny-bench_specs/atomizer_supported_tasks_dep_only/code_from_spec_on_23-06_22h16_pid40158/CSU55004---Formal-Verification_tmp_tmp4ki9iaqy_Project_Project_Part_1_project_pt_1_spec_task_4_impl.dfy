//IMPL isPrefix
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
    var i := 0;
    while i < |pre|
        invariant 0 <= i <= |pre|
        invariant forall j :: 0 <= j < i ==> str[j] == pre[j]
        invariant i <= |str|
    {
        if str[i] != pre[i] {
            res := false;
            return;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 4): set res after loop completes successfully */
    res := true;
}

//IMPL isSubstring
//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
{
    var i := 0;
    while i <= |str| - |sub|
        invariant 0 <= i <= |str| - |sub| + 1
    {
        var j := 0;
        var match := true;
        while j < |sub| && match
            invariant 0 <= j <= |sub|
            invariant match ==> forall k :: 0 <= k < j ==> str[i + k] == sub[k]
            /* code modified by LLM (iteration 4): fix bounds invariant to ensure i + j < |str| */
            invariant i + |sub| <= |str|
        {
            /* code modified by LLM (iteration 4): simplified bounds check - we know i + j < |str| from outer loop */
            if str[i + j] != sub[j] {
                match := false;
            } else {
                j := j + 1;
            }
        }
        /* code modified by LLM (iteration 4): check if we found complete match */
        if match && j == |sub| {
            res := true;
            return;
        }
        i := i + 1;
    }
    res := false;
}

//IMPL haveCommonKSubstring
//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
    requires 0 < k <= |str1| &&  0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
{
    var i := 0;
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
    {
        /* code modified by LLM (iteration 4): ensure bounds before slicing */
        assert i + k <= |str1|;
        var sub1 := str1[i..i+k];
        var j := 0;
        while j <= |str2| - k
            invariant 0 <= j <= |str2| - k + 1
        {
            /* code modified by LLM (iteration 4): ensure bounds before slicing */
            assert j + k <= |str2|;
            var sub2 := str2[j..j+k];
            if sub1 == sub2 {
                found := true;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    found := false;
}

//IMPL maxCommonSubstringLength
//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
method maxCommonSubstringLength(str1:string, str2:string) returns(len:nat)
    requires 0 < |str1| && 0 < |str2|
{
    len := 0;
    var maxLen := if |str1| < |str2| then |str1| else |str2|;
    var k := 1;
    
    while k <= maxLen
        invariant 1 <= k <= maxLen + 1
        invariant 0 <= len < k
        /* code modified by LLM (iteration 4): simplified invariants for verification */
        invariant len == 0 || haveCommonSubstringOfLength(len, str1, str2)
    {
        /* code modified by LLM (iteration 4): use existing haveCommonKSubstring method */
        var hasCommon := haveCommonKSubstring(k, str1, str2);
        
        if hasCommon {
            len := k;
        }
        k := k + 1;
    }
}

/* code modified by LLM (iteration 4): add helper predicate for verification */
predicate haveCommonSubstringOfLength(k: nat, str1: string, str2: string)
    requires k <= |str1| && k <= |str2|
{
    exists i, j :: 0 <= i <= |str1| - k && 0 <= j <= |str2| - k && str1[i..i+k] == str2[j..j+k]
}

//ATOM_PLACEHOLDER_Main