// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ReverseString(s: array<char>) returns (result: array<char>)
    ensures
        result.Length == s.Length &&
        forall i :: 0 <= i < s.Length ==> result[i] == s[s.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
  result := new char[s.Length];
  var n := s.Length;
  for i := 0 to n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> result[k] == s[n - 1 - k]
  {
    result[i] := s[n - 1 - i];
  }
}
// </vc-code>
