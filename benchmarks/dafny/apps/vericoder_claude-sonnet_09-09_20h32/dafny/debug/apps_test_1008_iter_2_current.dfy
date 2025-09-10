function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

// <vc-helpers>
lemma SubstringBounds(s: string, start: int, end: int)
    requires 0 <= start <= end <= |s|
    ensures |s[start..end]| == end - start
{
}

lemma DivisionProperties(n: int, k: int)
    requires k > 0
    requires n >= 0
    ensures n / k >= 0
    ensures k > 0 && n % k == 0 ==> k * (n / k) == n
{
}

lemma ChunkBounds(s: string, k: int, i: int)
    requires k > 0
    requires |s| % k == 0
    requires 0 <= i < k
    ensures 0 <= i * (|s| / k) <= (i + 1) * (|s| / k) <= |s|
{
    var chunkSize := |s| / k;
    assert chunkSize >= 0;
    assert k * chunkSize == |s|;
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
    DivisionProperties(|s|, k);
    
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant forall j :: 0 <= j < i ==> isPalindrome(s[j * chunkSize..(j + 1) * chunkSize])
    {
        ChunkBounds(s, k, i);
        var start := i * chunkSize;
        var end := (i + 1) * chunkSize;
        
        SubstringBounds(s, start, end);
        var chunk := s[start..end];
        
        if !isPalindrome(chunk) {
            return "NO";
        }
        i := i + 1;
    }
    
    return "YES";
}
// </vc-code>

