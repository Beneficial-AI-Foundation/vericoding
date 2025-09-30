// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function MinLength(a: array<char>, b: array<char>): nat
  reads a, b
{
  if a.Length <= b.Length then a.Length else b.Length
}

function CommonPrefixLength(str1: array<char>, str2: array<char>): nat
  reads str1, str2
  ensures CommonPrefixLength(str1, str2) <= str1.Length
  ensures CommonPrefixLength(str1, str2) <= str2.Length
  ensures forall i :: 0 <= i < CommonPrefixLength(str1, str2) ==> str1[i] == str2[i]
  ensures CommonPrefixLength(str1, str2) == str1.Length || CommonPrefixLength(str1, str2) == str2.Length ||
    (CommonPrefixLength(str1, str2) < str1.Length && CommonPrefixLength(str1, str2) < str2.Length && 
     str1[CommonPrefixLength(str1, str2)] != str2[CommonPrefixLength(str1, str2)])
{
  CommonPrefixLengthHelper(str1, str2, 0)
}

function CommonPrefixLengthHelper(str1: array<char>, str2: array<char>, i: nat): nat
  reads str1, str2
  requires i <= str1.Length && i <= str2.Length
  ensures CommonPrefixLengthHelper(str1, str2, i) <= str1.Length
  ensures CommonPrefixLengthHelper(str1, str2, i) <= str2.Length
  ensures CommonPrefixLengthHelper(str1, str2, i) >= i
  ensures forall j :: i <= j < CommonPrefixLengthHelper(str1, str2, i) ==> str1[j] == str2[j]
  ensures CommonPrefixLengthHelper(str1, str2, i) == str1.Length || CommonPrefixLengthHelper(str1, str2, i) == str2.Length ||
    (CommonPrefixLengthHelper(str1, str2, i) < str1.Length && CommonPrefixLengthHelper(str1, str2, i) < str2.Length && 
     str1[CommonPrefixLengthHelper(str1, str2, i)] != str2[CommonPrefixLengthHelper(str1, str2, i)])
  decreases str1.Length - i, str2.Length - i
{
  if i == str1.Length || i == str2.Length then
    i
  else if str1[i] != str2[i] then
    i
  else
    CommonPrefixLengthHelper(str1, str2, i + 1)
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
  var len := CommonPrefixLength(str1, str2);
  result := new char[len];
  var i := 0;
  while i < len
    invariant 0 <= i <= len
    invariant forall j :: 0 <= j < i ==> result[j] == str1[j] && result[j] == str2[j]
  {
    result[i] := str1[i];
    i := i + 1;
  }
}
// </vc-code>
