// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LongestCommonPrefix(str1: array<char>, str2: array<char>) returns (result: array<char>)
    ensures
        result.Length <= str1.Length &&
        result.Length <= str2.Length &&
        (forall i :: 0 <= i < result.Length ==> result[i] == str1[i] && result[i] == str2[i]) &&
        (result.Length == str1.Length || result.Length == str2.Length || 
            (result.Length < str1.Length && result.Length < str2.Length && str1[result.Length] != str2[result.Length]))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): removed deprecated semicolon from invariant */
    var i: nat := 0;
    while i < str1.Length && i < str2.Length && str1[i] == str2[i]
        invariant 0 <= i <= str1.Length
        invariant 0 <= i <= str2.Length
        invariant forall j :: 0 <= j < i ==> str1[j] == str2[j]
    {
        i := i + 1;
    }

    result := new char[i];

    var k: nat := 0;
    while k < i
        invariant 0 <= k <= i
        invariant forall j :: 0 <= j < k ==> result[j] == str1[j]
    {
        result[k] := str1[k];
        k := k + 1;
    }
}
// </vc-code>
