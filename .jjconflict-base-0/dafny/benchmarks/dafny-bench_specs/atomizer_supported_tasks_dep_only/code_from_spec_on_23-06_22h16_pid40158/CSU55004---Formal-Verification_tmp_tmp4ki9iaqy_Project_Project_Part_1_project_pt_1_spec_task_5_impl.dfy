//IMPL isPrefix
//This method should return true iff pre is a prefix of str. That is, str starts with pre
method isPrefix(pre:string, str:string) returns(res:bool)
    requires 0 < |pre| <= |str| //This line states that this method requires that pre is less than or equal in length to str. Without this line, an out of bounds error is shown on line 14: "str[i] != pre[i]"
    ensures res <==> (forall j :: 0 <= j < |pre| ==> str[j] == pre[j])
{
    /* code modified by LLM (iteration 4): fix loop invariant and ensure postcondition */
    res := true;
    var i := 0;
    while i < |pre|
        invariant 0 <= i <= |pre|
        invariant res <==> (forall j :: 0 <= j < i ==> str[j] == pre[j])
    {
        if str[i] != pre[i] {
            res := false;
            return;
        }
        i := i + 1;
    }
    // At this point, i == |pre| and res is still true
    // The invariant guarantees (forall j :: 0 <= j < |pre| ==> str[j] == pre[j])
}

//IMPL isSubstring
//This method should return true iff sub is a substring of str. That is, str contains sub
method isSubstring(sub:string, str:string) returns(res:bool)
    requires 0 < |sub| <= |str| //This method requires that sub is less than or equal in length to str
    ensures res <==> (exists i :: 0 <= i <= |str| - |sub| && (forall j :: 0 <= j < |sub| ==> str[i + j] == sub[j]))
{
    /* code modified by LLM (iteration 4): fix invariants to properly maintain the postcondition */
    res := false;
    var i := 0;
    while i <= |str| - |sub|
        invariant 0 <= i <= |str| - |sub| + 1
        invariant res ==> (exists idx :: 0 <= idx <= |str| - |sub| && (forall j :: 0 <= j < |sub| ==> str[idx + j] == sub[j]))
        invariant !res ==> (forall idx :: 0 <= idx < i ==> (exists j :: 0 <= j < |sub| && str[idx + j] != sub[j]))
    {
        var j := 0;
        var match := true;
        while j < |sub| && match
            invariant 0 <= j <= |sub|
            invariant match <==> (forall k :: 0 <= k < j ==> str[i + k] == sub[k])
        {
            if str[i + j] != sub[j] {
                match := false;
            } else {
                j := j + 1;
            }
        }
        if match {
            res := true;
            return;
        }
        i := i + 1;
    }
}

//IMPL haveCommonKSubstring
//This method should return true iff str1 and str1 have a common substring of length k
method haveCommonKSubstring(k:nat, str1:string, str2:string) returns(found:bool)
    requires 0 < k <= |str1| &&  0 < k <= |str2| //This method requires that k > 0 and k is less than or equal to in length to str1 and str2
    ensures found <==> (exists i, j :: 0 <= i <= |str1| - k && 0 <= j <= |str2| - k && 
                       (forall p :: 0 <= p < k ==> str1[i + p] == str2[j + p]))
{
    /* code modified by LLM (iteration 4): fix nested loop invariants to maintain postcondition */
    found := false;
    var i := 0;
    while i <= |str1| - k && !found
        invariant 0 <= i <= |str1| - k + 1
        invariant found ==> (exists idx, jdx :: 0 <= idx <= |str1| - k && 0 <= jdx <= |str2| - k && 
                           (forall p :: 0 <= p < k ==> str1[idx + p] == str2[jdx + p]))
        invariant !found ==> (forall idx :: 0 <= idx < i ==> 
                             (forall j :: 0 <= j <= |str2| - k ==> 
                              (exists p :: 0 <= p < k && str1[idx + p] != str2[j + p])))
    {
        var j := 0;
        while j <= |str2| - k && !found
            invariant 0 <= j <= |str2| - k + 1
            invariant found ==> (exists idx, jdx :: 0 <= idx <= |str1| - k && 0 <= jdx <= |str2| - k && 
                               (forall p :: 0 <= p < k ==> str1[idx + p] == str2[jdx + p]))
            invariant !found ==> (forall jdx :: 0 <= jdx < j ==> 
                                 (exists p :: 0 <= p < k && str1[i + p] != str2[jdx + p]))
        {
            var match := true;
            var pos := 0;
            while pos < k && match
                invariant 0 <= pos <= k
                invariant match <==> (forall p :: 0 <= p < pos ==> str1[i + p] == str2[j + p])
            {
                if str1[i + pos] != str2[j + pos] {
                    match := false;
                } else {
                    pos := pos + 1;
                }
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

//IMPL maxCommonSubstringLength
//This method should return the natural number len which is equal to the length of the longest common substring of str1 and str2. Note that every two strings have a common substring of length zero.
method maxCommonSubstringLength(str1:string, str2:string) returns(len:nat)
    requires 0 < |str1| && 0 < |str2|
    ensures len <= |str1| && len <= |str2|
    ensures len == 0 || (exists i, j :: 0 <= i <= |str1| - len && 0 <= j <= |str2| - len && 
                        (forall p :: 0 <= p < len ==> str1[i + p] == str2[j + p]))
    ensures forall l :: l > len ==> !(exists i, j :: 0 <= i <= |str1| - l && 0 <= j <= |str2| - l && 
                                     (forall p :: 0 <= p < l ==> str1[i + p] == str2[j + p]))
{
    /* code modified by LLM (iteration 4): fix algorithm by searching from length 1 upward */
    len := 0;
    var maxLen := if |str1| < |str2| then |str1| else |str2|;
    var currentLen := 1;
    
    while currentLen <= maxLen
        invariant 1 <= currentLen <= maxLen + 1
        invariant len <= maxLen
        invariant len == 0 || (exists i, j :: 0 <= i <= |str1| - len && 0 <= j <= |str2| - len && 
                              (forall p :: 0 <= p < len ==> str1[i + p] == str2[j + p]))
        invariant forall l :: len < l < currentLen ==> 
                 !(exists i, j :: 0 <= i <= |str1| - l && 0 <= j <= |str2| - l && 
                   (forall p :: 0 <= p < l ==> str1[i + p] == str2[j + p]))
        decreases maxLen - currentLen
    {
        var i := 0;
        var foundAtCurrentLen := false;
        
        while i <= |str1| - currentLen && !foundAtCurrentLen
            invariant 0 <= i <= |str1| - currentLen + 1
            invariant foundAtCurrentLen ==> (exists idx, j :: 0 <= idx < i && 0 <= j <= |str2| - currentLen && 
                                           (forall p :: 0 <= p < currentLen ==> str1[idx + p] == str2[j + p]))
            invariant !foundAtCurrentLen ==> (forall idx :: 0 <= idx < i ==> 
                                             (forall j :: 0 <= j <= |str2| - currentLen ==> 
                                              (exists p :: 0 <= p < currentLen && str1[idx + p] != str2[j + p])))
        {
            var j := 0;
            while j <= |str2| - currentLen && !foundAtCurrentLen
                invariant 0 <= j <= |str2| - currentLen + 1
                invariant foundAtCurrentLen ==> (exists jdx :: 0 <= jdx < j && 
                                               (forall p :: 0 <= p < currentLen ==> str1[i + p] == str2[jdx + p]))
                invariant !foundAtCurrentLen ==> (forall jdx :: 0 <= jdx < j ==> 
                                                 (exists p :: 0 <= p < currentLen && str1[i + p] != str2[jdx + p]))
            {
                var match := true;
                var pos := 0;
                while pos < currentLen && match
                    invariant 0 <= pos <= currentLen
                    invariant match <==> (forall p :: 0 <= p < pos ==> str1[i + p] == str2[j + p])
                {
                    if str1[i + pos] != str2[j + pos] {
                        match := false;
                    } else {
                        pos := pos + 1;
                    }
                }
                if match {
                    len := currentLen;
                    foundAtCurrentLen := true;
                }
                j := j + 1;
            }
            i := i + 1;
        }
        currentLen := currentLen + 1;
    }
}

//IMPL Main
//Main to test each method
method Main(){
    /* code modified by LLM (iteration 4): keep the fixed method calls */
    var result1 := isPrefix("hello", "hello world");
    var result2 := isSubstring("world", "hello world");
    var result3 := haveCommonKSubstring(2, "abc", "bcd");
    var result4 := maxCommonSubstringLength("abcd", "bcde");
    
    print "isPrefix test: ", result1, "\n";
    print "isSubstring test: ", result2, "\n";
    print "haveCommonKSubstring test: ", result3, "\n";
    print "maxCommonSubstringLength test: ", result4, "\n";
}