

// <vc-helpers>
predicate InString(c: char, s: string)
{
  exists i | 0 <= i < |s| :: s[i] == c
}

lemma CharacterInStringPreservation(s: string, c: char, i: int)
  requires 0 <= i < |s|
  ensures s[i] in s
{
}

lemma CharacterNotInString(s: string, c: char)
  ensures !(c in s) ==> forall i | 0 <= i < |s| :: s[i] != c
{
}
// </vc-helpers>

// <vc-spec>
method RemoveChars(s1: string, s2: string) returns (v: string)
    ensures |v| <= |s1|
    ensures forall i :: 0 <= i < |v| ==> (v[i] in s1) && !(v[i] in s2)
    ensures forall i :: 0 <= i < |s1| ==> (s1[i] in s2) || (s1[i] in v)
// </vc-spec>
// <vc-code>
{
  var result: seq<char> := [];
  var i := 0;
  
  while i < |s1|
    invariant 0 <= i <= |s1|
    invariant |result| <= i
    invariant forall j :: 0 <= j < |result| ==> (result[j] in s1) && !(result[j] in s2)
    invariant forall k :: 0 <= k < i ==> (s1[k] in s2) || (s1[k] in result)
  {
    var currentChar := s1[i];
    if !InString(currentChar, s2) {
      result := result + [currentChar];
    }
    i := i + 1;
  }
  
  v := result;
}
// </vc-code>

