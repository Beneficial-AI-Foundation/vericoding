function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

// <vc-helpers>
lemma PalindromeCheckCorrect(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    ensures isPalindrome(s[start..end]) <==> 
        forall i :: 0 <= i < (end - start) / 2 ==> s[start + i] == s[end - 1 - i]
{
    var substr := s[start..end];
    assert |substr| == end - start;
    forall i | 0 <= i < |substr| / 2
        ensures substr[i] == substr[|substr| - 1 - i] <==> s[start + i] == s[end - 1 - i]
    {
        assert substr[i] == s[start + i];
        assert substr[|substr| - 1 - i] == s[start + (end - start) - 1 - i] == s[end - 1 - i];
    }
}
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: string)
    requires k > 0
    ensures result == "YES" || result == "NO"
    ensures |s| % k != 0 ==> result == "NO"
    ensures |s| % k == 0 && (forall i :: 0 <= i < k ==> 
        isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "YES"
    ensures |s| % k == 0 && (exists i :: 0 <= i < k && 
        !isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "NO"
// </vc-spec>
// <vc-code>
{
    if |s| % k != 0 {
        return "NO";
    }
    
    var chunkSize := |s| / k;
    var i := 0;
    
    while i < k
        invariant 0 <= i <= k
        invariant forall j :: 0 <= j < i ==> isPalindrome(s[j * chunkSize..(j + 1) * chunkSize])
    {
        var start := i * chunkSize;
        var end := (i + 1) * chunkSize;
        
        var j := 0;
        var isPalin := true;
        
        while j < chunkSize / 2
            invariant 0 <= j <= chunkSize / 2
            invariant isPalin <==> forall m :: 0 <= m < j ==> s[start + m] == s[end - 1 - m]
        {
            if s[start + j] != s[end - 1 - j] {
                isPalin := false;
                break;
            }
            j := j + 1;
        }
        
        if !isPalin {
            PalindromeCheckCorrect(s, start, end);
            return "NO";
        }
        
        PalindromeCheckCorrect(s, start, end);
        i := i + 1;
    }
    
    return "YES";
}
// </vc-code>

