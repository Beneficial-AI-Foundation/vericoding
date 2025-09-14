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
    /* code modified by LLM (iteration 2): fixed compilation error by replacing the array initializer lambda with an explicit copy loop. */
    var i := 0;
    while i < str1.Length && i < str2.Length && str1[i] == str2[i]
        invariant 0 <= i <= str1.Length
        invariant 0 <= i <= str2.Length
        invariant forall k :: 0 <= k < i ==> str1[k] == str2[k]
    {
        i := i + 1;
    }
    result := new char[i];
    var j := 0;
    while j < i
        invariant 0 <= j <= i
        invariant forall k :: 0 <= k < j ==> result[k] == str1[k]
        invariant forall k :: 0 <= k < i ==> str1[k] == str2[k]
    {
        result[j] := str1[j];
        j := j + 1;
    }
}
// </vc-code>
