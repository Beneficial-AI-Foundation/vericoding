// <vc-helpers>
// No additional helper code or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
// </vc-spec>
// </vc-spec>

// <vc-code>
method LongestCommonPrefixImpl(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|] && |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix| == |str1| || |prefix| == |str2| || (str1[|prefix|] != str2[|prefix|])
{
  var i := 0;
  while i < |str1| && i < |str2| && str1[i] == str2[i]
    invariant 0 <= i <= |str1| && 0 <= i <= |str2|
    invariant forall k :: 0 <= k < i ==> str1[k] == str2[k]
  {
    i := i + 1;
  }
  prefix := str1[0..i];
}
// </vc-code>
