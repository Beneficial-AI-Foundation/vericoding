// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function ArraySliceEq(a: array<char>, aStart: int, b: array<char>, bStart: int, length: int): bool
    requires 0 <= aStart && 0 <= bStart && 0 <= length
    requires aStart + length <= a.Length
    requires bStart + length <= b.Length
    decreases length
    reads a, b
{
    if length <= 0 then true
    else if a[aStart] != b[bStart] then false
    else ArraySliceEq(a, aStart + 1, b, bStart + 1, length - 1)
}

function FindCommonPrefixLengthHelper(str1: array<char>, str2: array<char>, idx: int): (len: int)
    requires 0 <= idx <= str1.Length
    requires idx <= str2.Length
    ensures len >= idx
    ensures len <= str1.Length && len <= str2.Length
    ensures forall i :: idx <= i < len ==> str1[i] == str2[i]
    ensures len == str1.Length || len == str2.Length || (len < str1.Length && len < str2.Length && str1[len] != str2[len])
    decreases str1.Length - idx + str2.Length - idx
    reads str1, str2
{
    if idx < str1.Length && idx < str2.Length && str1[idx] == str2[idx] then
        FindCommonPrefixLengthHelper(str1, str2, idx + 1)
    else
        idx
}

function FindCommonPrefixLength(str1: array<char>, str2: array<char>): (len: int)
    ensures 0 <= len <= str1.Length && len <= str2.Length
    ensures forall i :: 0 <= i < len ==> str1[i] == str2[i]
    ensures len == str1.Length || len == str2.Length || (len < str1.Length && len < str2.Length && str1[len] != str2[len])
    reads str1, str2
{
    FindCommonPrefixLengthHelper(str1, str2, 0)  
}

function min(a: int, b: int): int {
    if a < b then a else b
}
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
    /* code modified by LLM (iteration 3): Fixed array slice validation */
    var commonLength := FindCommonPrefixLength(str1, str2);
    var resultArray := new char[commonLength];
    
    var i := 0;
    while i < commonLength
        invariant 0 <= i <= commonLength
        invariant forall j :: 0 <= j < i ==> resultArray[j] == str1[j] && resultArray[j] == str2[j]
    {
        resultArray[i] := str1[i];
        i := i + 1;
    }
    
    result := resultArray;
}
// </vc-code>
