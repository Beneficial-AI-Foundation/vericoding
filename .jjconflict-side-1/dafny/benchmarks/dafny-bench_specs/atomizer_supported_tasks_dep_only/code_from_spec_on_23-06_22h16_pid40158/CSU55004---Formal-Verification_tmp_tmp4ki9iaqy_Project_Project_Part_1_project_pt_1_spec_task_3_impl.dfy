//IMPL isPrefix
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
    res := true;
    var i := 0;
    while i < |pre|
        invariant 0 <= i <= |pre|
        invariant res <==> forall j :: 0 <= j < i ==> str[j] == pre[j]
    {
        if str[i] != pre[i] {
            res := false;
            return;
        }
        i := i + 1;
    }
}

/* code modified by LLM (iteration 1): Added helper predicate for substring matching */
predicate isMatchAt(str: string, sub: string, pos: int)
    requires 0 <= pos
    requires |sub| > 0
{
    pos + |sub| <= |str| && forall j :: 0 <= j < |sub| ==> str[pos + j] == sub[j]
}

//IMPL isSubstring
//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
{
    res := false;
    var i := 0;
    while i <= |str| - |sub|
        invariant 0 <= i <= |str| - |sub| + 1
        /* code modified by LLM (iteration 1): Fixed invariant to properly track no match found so far */
        invariant !res ==> forall k :: 0 <= k < i ==> !isMatchAt(str, sub, k)
    {
        var match := true;
        var j := 0;
        while j < |sub| && match
            invariant 0 <= j <= |sub|
            invariant match <==> forall l :: 0 <= l < j ==> str[i + l] == sub[l]
        {
            if str[i + j] != sub[j] {
                match := false;
            }
            j := j + 1;
        }
        if match {
            res := true;
            return;
        }
        i := i + 1;
    }
}

/* code modified by LLM (iteration 1): Added helper predicates for k-substring matching */
predicate kSubstringsMatch(str1: string, str2: string, k: nat, i: int, j: int)
    requires k > 0
    requires 0 <= i && 0 <= j
{
    i + k <= |str1| && j + k <= |str2| && forall l :: 0 <= l < k ==> str1[i + l] == str2[j + l]
}

predicate hasKSubstringMatch(str1: string, str2: string, k: nat, i: int)
    requires k > 0
    requires 0 <= i
{
    i + k <= |str1| && exists j :: 0 <= j <= |str2| - k && kSubstringsMatch(str1, str2, k, i, j)
}

//IMPL haveCommonKSubstring
//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
    requires 0 < k <= |str1| &&  0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
{
    found := false;
    var i := 0;
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        /* code modified by LLM (iteration 1): Fixed invariant using helper predicate */
        invariant !found ==> forall i' :: 0 <= i' < i ==> !hasKSubstringMatch(str1, str2, k, i')
    {
        var j := 0;
        while j <= |str2| - k && !found
            invariant 0 <= j <= |str2| - k + 1
            /* code modified by LLM (iteration 1): Fixed inner loop invariant */
            invariant !found ==> forall j' :: 0 <= j' < j ==> !kSubstringsMatch(str1, str2, k, i, j')
        {
            var match := true;
            var l := 0;
            while l < k && match
                invariant 0 <= l <= k
                invariant match <==> forall m :: 0 <= m < l ==> str1[i + m] == str2[j + m]
            {
                if str1[i + l] != str2[j + l] {
                    match := false;
                }
                l := l + 1;
            }
            if match {
                found := true;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}

//ATOM_PLACEHOLDER_maxCommonSubstringLength

//ATOM_PLACEHOLDER_Main