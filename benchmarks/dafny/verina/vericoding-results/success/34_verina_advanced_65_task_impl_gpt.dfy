// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): replaced 'function method' with 'function' and kept index validity specifications */
function RevIndex(n: int, i: int): int
  requires 0 <= i < n
  ensures 0 <= RevIndex(n, i) < n
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
  /* code modified by LLM (iteration 2): implement reversal using loop and RevIndex helper */
  var n := s.Length;
  result := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant forall k :: 0 <= k < i ==> result[k] == s[n - 1 - k]
  {
    var j := RevIndex(n, i);
    result[i] := s[j];
    i := i + 1;
  }
}
// </vc-code>
