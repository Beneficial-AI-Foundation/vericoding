

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method isPalindrome(s: array<char>) returns (result: bool)
    requires 1<= s.Length <= 200000
    ensures result <==> (forall i:: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
// </vc-spec>
// <vc-code>
{
    var n := s.Length;
    var i := 0;
    
    while i < n / 2
        invariant 0 <= i <= n / 2
        invariant forall j :: 0 <= j < i ==> s[j] == s[n - 1 - j]
    {
        if s[i] != s[n - 1 - i] {
            return false;
        }
        i := i + 1;
    }
    
    return true;
}
// </vc-code>

