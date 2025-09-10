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

lemma CheckPalindromeSimple(s: string, start: int, end: int, checkPos: int)
    requires 0 <= start <= end <= |s|
    requires 0 <= checkPos <= (end - start) / 2
    requires forall m :: 0 <= m < checkPos ==> s[start + m] == s[end - 1 - m]
    ensures checkPos == (end - start) / 2 ==> isPalindrome(s[start..end])
{
    if checkPos == (end - start) / 2 {
        PalindromeCheckCorrect(s, start, end);
    }
}

lemma ChunkBoundsValid(s: string, k: int, i: int, chunkSize: int)
    requires k > 0
    requires |s| > 0
    requires |s| % k == 0
    requires chunkSize == |s| / k
    requires 0 <= i < k
    ensures i * chunkSize >= 0
    ensures (i + 1) * chunkSize <= |s|
    ensures i * chunkSize < (i + 1) * chunkSize
    ensures chunkSize > 0
{
    assert chunkSize > 0 by {
        assert |s| > 0;
        assert chunkSize * k == |s|;
        assert k > 0;
    }
    assert (i + 1) * chunkSize == i * chunkSize + chunkSize;
    assert (i + 1) * chunkSize <= k * chunkSize == |s|;
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
    
    if |s| == 0 {
        return "YES";
    }
    
    var chunkSize := |s| / k;
    assert chunkSize * k == |s|;
    assert chunkSize > 0;
    var i := 0;
    
    while i < k
        invariant 0 <= i <= k
        invariant chunkSize == |s| / k
        invariant chunkSize > 0
        invariant chunkSize * k == |s|
        invariant forall j :: 0 <= j < i ==> isPalindrome(s[j * chunkSize..(j + 1) * chunkSize])
    {
        ChunkBoundsValid(s, k, i, chunkSize);
        var start := i * chunkSize;
        var end := (i + 1) * chunkSize;
        assert 0 <= start < end <= |s|;
        
        var j := 0;
        var isPalin := true;
        
        while j < chunkSize / 2
            invariant 0 <= j <= chunkSize / 2
            invariant isPalin <==> (forall m :: 0 <= m < j ==> s[start + m] == s[end - 1 - m])
        {
            if s[start + j] != s[end - 1 - j] {
                isPalin := false;
                PalindromeCheckCorrect(s, start, end);
                assert !isPalindrome(s[start..end]);
                return "NO";
            }
            j := j + 1;
        }
        
        assert j == chunkSize / 2;
        assert isPalin;
        CheckPalindromeSimple(s, start, end, j);
        assert isPalindrome(s[start..end]);
        
        i := i + 1;
    }
    
    assert i == k;
    return "YES";
}
// </vc-code>

