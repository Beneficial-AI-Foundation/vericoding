

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LongestCommonPrefix(str1: seq<char>, str2: seq<char>) returns (prefix: seq<char>)
  ensures |prefix| <= |str1| && prefix == str1[0..|prefix|]&& |prefix| <= |str2| && prefix == str2[0..|prefix|]
  ensures |prefix|==|str1| || |prefix|==|str2| || (str1[|prefix|]!=str2[|prefix|])
// </vc-spec>
// <vc-code>
{
  prefix := [];
  var i := 0;
  while i < |str1| && i < |str2| && str1[i] == str2[i]
    invariant 0 <= i <= |str1|
    invariant 0 <= i <= |str2|
    invariant prefix == str1[0..i]
    invariant prefix == str2[0..i]
  {
    prefix := prefix + [str1[i]];
    i := i + 1;
  }
}
// </vc-code>

