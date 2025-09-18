// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clause to predicate */
predicate IsReverse(s: array<char>, t: array<char>) reads s, t
{
    s.Length == t.Length &&
    (forall i :: 0 <= i < s.Length ==> s[i] == t[s.Length - 1 - i])
}
// </vc-helpers>

// <vc-spec>
method ReverseString(s: array<char>) returns (result: array<char>)
    ensures
        result.Length == s.Length &&
        forall i :: 0 <= i < s.Length ==> result[i] == s[s.Length - 1 - i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed code to use correct array indexing */
{
    var n := s.Length;
    result := new char[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> result[k] == s[n - 1 - k]
        decreases n - i
    {
        result[i] := s[n - 1 - i];
        i := i + 1;
    }
}
// </vc-code>
