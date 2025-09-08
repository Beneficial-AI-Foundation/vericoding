Given a string s and an integer k, determine if s can be split into exactly k
palindromes of equal length. Return "YES" if possible, "NO" otherwise.

function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

method solve(s: string, k: int) returns (result: string)
    requires k > 0
    ensures result == "YES" || result == "NO"
    ensures |s| % k != 0 ==> result == "NO"
    ensures |s| % k == 0 && (forall i :: 0 <= i < k ==> 
        isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "YES"
    ensures |s| % k == 0 && (exists i :: 0 <= i < k && 
        !isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "NO"
{
    if |s| % k != 0 {
        result := "NO";
        return;
    }

    var step := |s| / k;
    var i := 0;
    while i < k
        invariant 0 <= i <= k
        invariant forall j :: 0 <= j < i ==> isPalindrome(s[j * step..(j + 1) * step])
        invariant step == |s| / k
        invariant |s| % k == 0
    {
        var start := i * step;
        var end := (i + 1) * step;
        var substring := s[start..end];

        if !isPalindrome(substring) {
            result := "NO";
            return;
        }

        i := i + 1;
    }

    result := "YES";
}
