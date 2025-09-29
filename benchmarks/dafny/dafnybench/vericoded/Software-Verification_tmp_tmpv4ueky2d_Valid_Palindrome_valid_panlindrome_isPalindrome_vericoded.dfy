// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method isPalindrome(s: array<char>) returns (result: bool)
    requires 1<= s.Length <= 200000
    ensures result <==> (forall i:: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < s.Length / 2
    invariant 0 <= i <= s.Length / 2
    invariant forall k :: 0 <= k < i ==> s[k] == s[s.Length - 1 - k]
  {
    if s[i] != s[s.Length - 1 - i]
    {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
