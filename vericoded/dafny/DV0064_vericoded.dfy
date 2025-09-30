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
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> result[j] == s[s.Length - 1 - j]
  {
    result[i] := s[s.Length - 1 - i];
    i := i + 1;
  }
}
// </vc-code>
