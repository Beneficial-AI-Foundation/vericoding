

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method isPalindrome(s: array<char>) returns (result: bool)
    requires 1<= s.Length <= 200000
    ensures result <==> (forall i:: 0 <= i < s.Length / 2 ==> s[i] == s[s.Length - 1 - i])
// </vc-spec>
// <vc-code>
{
  result := true;
  var i := 0;
  var n := s.Length;
  while i < n / 2 && s[i] == s[n - 1 - i]
    invariant 0 <= i <= n / 2
    invariant forall k :: 0 <= k < i ==> s[k] == s[n - 1 - k]
    decreases n / 2 - i
  {
    i := i + 1;
  }
  result := (i == n / 2);
}
// </vc-code>

