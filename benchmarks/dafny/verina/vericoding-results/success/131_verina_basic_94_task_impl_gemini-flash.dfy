// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// No helpers needed for this method.
// </vc-helpers>

// <vc-spec>
method IterCopy(s: array<int>) returns (result: array<int>)
    ensures
        s.Length == result.Length &&
        forall i :: 0 <= i < s.Length ==> s[i] == result[i]
// </vc-spec>
// <vc-code>
{
    result := new int[s.Length];
    var i := 0;
    while i < s.Length
        invariant 0 <= i <= s.Length
        invariant forall k :: 0 <= k < i ==> s[k] == result[k]
    {
        result[i] := s[i];
        i := i + 1;
    }
}
// </vc-code>
