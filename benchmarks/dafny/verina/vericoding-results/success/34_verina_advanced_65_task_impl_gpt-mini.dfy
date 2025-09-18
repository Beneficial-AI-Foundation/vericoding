// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Compute reversed index ensuring bounds */
function ReverseIndex(n: int, i: int): int
  requires 0 <= i < n
  requires n >= 0
  ensures 0 <= n - 1 - i < n
{
  n - 1 - i
}
// </vc-helpers>

// <vc-spec>
method ReverseString(s: array<char>) returns (result: array<char>)
    ensures
        result.Length == s.Length &&
        forall i :: 0 <= i < s.Length ==> result[i] == s[s.Length - 1 - i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): Reverse array by filling result left-to-right */
  result := new char[s.Length];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> result[j] == s[s.Length - 1 - j]
  {
    result[i] := s[ReverseIndex(s.Length, i)];
    i := i + 1;
  }
}
// </vc-code>
