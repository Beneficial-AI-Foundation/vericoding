//IMPL isPrefix
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
{
    /* code modified by LLM (iteration 4): initialize res to true and fix invariant */
    res := true;
    var i := 0;
    while i < |pre|
        invariant 0 <= i <= |pre|
        invariant forall j :: 0 <= j < i ==> str[j] == pre[j]
        invariant res == true
    {
        if str[i] != pre[i] {
            res := false;
            return;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 4): res is already true from initialization */
}

//IMPL isSubstring
//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
{
    /* code modified by LLM (iteration 4): initialize res to false */
    res := false;
    var i := 0;
    while i <= |str| - |sub|
        invariant 0 <= i <= |str| - |sub| + 1
        invariant !res ==> forall start :: 0 <= start < i ==> exists pos :: 0 <= pos < |sub| && str[start + pos] != sub[pos]
    {
        var j := 0;
        var match := true;
        while j < |sub| && match
            invariant 0 <= j <= |sub|
            invariant match ==> forall k :: 0 <= k < j ==> str[i + k] == sub[k]
            /* code modified by LLM (iteration 4): fixed bounds invariant */
            invariant i + j <= |str|
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
    /* code modified by LLM (iteration 4): res remains false if no match found */
}

//IMPL haveCommonKSubstring
//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
    requires 0 < k <= |str1| &&  0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
{
    /* code modified by LLM (iteration 4): initialize found to false */
    found := false;
    var i := 0;
    while i <= |str1| - k
        invariant 0 <= i <= |str1| - k + 1
        invariant !found ==> forall start1 :: 0 <= start1 < i ==> forall start2 :: 0 <= start2 <= |str2| - k ==> exists pos :: 0 <= pos < k && str1[start1 + pos] != str2[start2 + pos]
    {
        var j := 0;
        while j <= |str2| - k
            invariant 0 <= j <= |str2| - k + 1
            invariant !found ==> forall start2 :: 0 <= start2 < j ==> exists pos :: 0 <= pos < k && str1[i + pos] != str2[start2 + pos]
        {
            var match := true;
            var m := 0;
            while m < k && match
                invariant 0 <= m <= k
                invariant match ==> forall n :: 0 <= n < m ==> str1[i + n] == str2[j + n]
                /* code modified by LLM (iteration 4): fixed bounds invariants */
                invariant i + m <= |str1|
                invariant j + m <= |str2|
            {
                if str1[i + m] != str2[j + m] {
                    match := false;
                }
                m := m + 1;
            }
            if match {
                found := true;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    /* code modified by LLM (iteration 4): found remains false if no match found */
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
        /* code modified by LLM (iteration 4): simplified decreases clause */
        decreases maxLen - k
    {
        var i := 0;
        var foundAtK := false;
        
        while i <= |str1| - k && !foundAtK
            invariant 0 <= i <= |str1| - k + 1
            /* code modified by LLM (iteration 4): simplified decreases clause */
            decreases |str1| - k - i
        {
            var j := 0;
            while j <= |str2| - k && !foundAtK
                invariant 0 <= j <= |str2| - k + 1
                /* code modified by LLM (iteration 4): simplified decreases clause */
                decreases |str2| - k - j
            {
                var match := true;
                var m := 0;
                while m < k && match
                    invariant 0 <= m <= k
                    invariant match ==> forall n :: 0 <= n < m ==> str1[i + n] == str2[j + n]
                    /* code modified by LLM (iteration 4): fixed bounds invariants */
                    invariant i + m <= |str1|
                    invariant j + m <= |str2|
                    decreases k - m
                {
                    if str1[i + m] != str2[j + m] {
                        match := false;
                    }
                    m := m + 1;
                }
                if match {
                    foundAtK := true;
                    len := k;
                }
                j := j + 1;
            }
            i := i + 1;
        }
        k := k + 1;
    }
}

//IMPL Main
//Main to test each method
method Main(){
    var result1 := isPrefix("hello", "hello world");
    print "isPrefix test: ", result1, "\n";
    
    var result2 := isSubstring("wor", "hello world");
    print "isSubstring test: ", result2, "\n";
    
    var result3 := haveCommonKSubstring(2, "hello", "world");
    print "haveCommonKSubstring test: ", result3, "\n";
    
    var result4 := maxCommonSubstringLength("hello", "world");
    print "maxCommonSubstringLength test: ", result4, "\n";
}