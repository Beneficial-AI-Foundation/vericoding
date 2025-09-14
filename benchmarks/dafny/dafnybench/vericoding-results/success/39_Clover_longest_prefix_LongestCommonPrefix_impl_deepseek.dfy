

// <vc-helpers>
lemma CommonPrefixLemma(str1: seq<char>, str2: seq<char>, n: nat)
  requires n <= |str1| && n <= |str2|
  ensures (forall i :: 0 <= i < n ==> str1[i] == str2[i]) ==> str1[0..n] == str2[0..n]
{
  if forall i :: 0 <= i < n ==> str1[i] == str2[i] {
    assert str1[0..n] == str2[0..n];
  }
}
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
    invariant 0 <= i <= |str1| && i <= |str2|
    invariant prefix == str1[0..i] && prefix == str2[0..i]
    invariant |prefix| == i
  {
    prefix := prefix + [str1[i]];
    i := i + 1;
  }
  // Post-condition proof
  if |prefix| < |str1| && |prefix| < |str2| {
    assert str1[|prefix|] != str2[|prefix|] by {
      if str1[|prefix|] == str2[|prefix|] {
        var j := |prefix|;
        assert j < |str1| && j < |str2| && str1[j] == str2[j];
        assert false; // Contradiction with loop condition
      }
    }
  }
  assert prefix == str1[0..|prefix|] && prefix == str2[0..|prefix|];
}
// </vc-code>

