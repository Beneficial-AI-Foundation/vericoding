

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
  var bad := -1;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant -1 <= bad < n
    invariant bad == -1 ==> (forall k :: 0 <= k < i ==> s[k] == s[n - 1 - k])
    invariant bad != -1 ==> s[bad] != s[n - 1 - bad]
    decreases n - 2 * i
  {
    if s[i] != s[n - 1 - i] {
      bad := i;
      i := n / 2;
    } else {
      i := i + 1;
    }
  }
  if bad == -1 {
    result := true;
  } else {
    result := false;
  }
}
// </vc-code>

