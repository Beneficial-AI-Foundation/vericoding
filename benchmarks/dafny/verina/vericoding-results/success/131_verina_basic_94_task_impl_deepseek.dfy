// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

method copy_array(s: array<int>) returns (result: array<int>)
    ensures s.Length == result.Length
    ensures forall i :: 0 <= i < s.Length ==> s[i] == result[i]
{
    result := new int[s.Length];
    var index := 0;
    while index < s.Length
        invariant 0 <= index <= s.Length
        invariant forall j :: 0 <= j < index ==> s[j] == result[j]
    {
        result[index] := s[index];
        index := index + 1;
    }
}

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
        invariant forall j :: 0 <= j < i ==> s[j] == result[j]
    {
        result[i] := s[i];
        i := i + 1;
    }
}
// </vc-code>
