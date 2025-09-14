

// <vc-helpers>
lemma PalindromeEquivalence(s: array<char>)
    requires s.Length >= 1
    ensures (forall i :: 0 <= i < s.Length ==> s[i] == s[s.Length - 1 - i]) <==> 
            (forall i :: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
{
    if forall i :: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i] {
        forall i | 0 <= i < s.Length
            ensures s[i] == s[s.Length - 1 - i]
        {
            if i < s.Length / 2 {
                // Already proven by assumption
            } else {
                var j := s.Length - 1 - i;
                assert j >= 0;
                if s.Length % 2 == 0 {
                    assert j < s.Length / 2;
                } else {
                    assert j <= s.Length / 2;
                    if j < s.Length / 2 {
                        assert s[j] == s[s.Length - 1 - j];
                    }
                }
                if j < s.Length / 2 {
                    assert s[j] == s[s.Length - 1 - j];
                    assert s[s.Length - 1 - j] == s[i];
                }
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method isPalindrome(s: array<char>) returns (result: bool)
    requires 1<= s.Length <= 200000
    ensures result <==> (forall i:: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
// </vc-spec>
// <vc-code>
{
    var left := 0;
    var right := s.Length - 1;
    
    while left < right
        invariant 0 <= left <= right + 1 <= s.Length
        invariant forall i :: 0 <= i < left ==> s[i] == s[s.Length - 1 - i]
        invariant forall i :: right < i < s.Length ==> s[i] == s[s.Length - 1 - i]
        invariant left + right == s.Length - 1
    {
        if s[left] != s[right] {
            result := false;
            return;
        }
        left := left + 1;
        right := right - 1;
    }
    
    assert forall i :: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i];
    result := true;
}
// </vc-code>

