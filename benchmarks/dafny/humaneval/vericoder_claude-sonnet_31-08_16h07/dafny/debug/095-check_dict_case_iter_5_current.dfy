function IsLowerCase(s: string) : bool
{
  forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}
function IsUpperCase(s: string) : bool
{
  forall i :: 0 <= i < |s| ==> 'A' <= s[i] <= 'Z'
}
type DictCase = map<string, string>

// <vc-helpers>
lemma EmptyMapHasNoKeys(dict: map<string, string>)
  ensures dict == map[] ==> forall k :: k !in dict
{
}

function SeqToSet<T>(s: seq<T>): set<T>
{
  set i | 0 <= i < |s| :: s[i]
}

lemma SeqToSetCorrect<T>(s: seq<T>)
  ensures forall x :: x in SeqToSet(s) <==> exists i :: 0 <= i < |s| && s[i] == x
{
}

lemma ExistsNotLowerCaseHelper(dict: DictCase, keySeq: seq<string>)
  requires forall k :: k in dict <==> k in keySeq
  requires exists i :: 0 <= i < |keySeq| && !IsLowerCase(keySeq[i])
  ensures !(forall k :: k in dict ==> IsLowerCase(k))
{
  var i :| 0 <= i < |keySeq| && !IsLowerCase(keySeq[i]);
  assert keySeq[i] in dict;
  assert !IsLowerCase(keySeq[i]);
}

lemma ExistsNotUpperCaseHelper(dict: DictCase, keySeq: seq<string>)
  requires forall k :: k in dict <==> k in keySeq
  requires exists i :: 0 <= i < |keySeq| && !IsUpperCase(keySeq[i])
  ensures !(forall k :: k in dict ==> IsUpperCase(k))
{
  var i :| 0 <= i < |keySeq| && !IsUpperCase(keySeq[i]);
  assert keySeq[i] in dict;
  assert !IsUpperCase(keySeq[i]);
}
// </vc-helpers>

// <vc-spec>
method CheckDictCase(dict: DictCase) returns (result: bool)
  // post-conditions-start
  ensures dict == map[] ==> !result
  ensures result ==> (forall k :: k in dict ==> IsLowerCase(k)) || (forall k :: k in dict ==> IsUpperCase(k))
  ensures !result ==> dict == map[] || ((exists k :: k in dict && !IsLowerCase(k)) && (exists k :: k in dict && !IsUpperCase(k)))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if dict == map[] {
    result := false;
    return;
  }
  
  var allLower := true;
  var allUpper := true;
  var hasNonLower := false;
  var hasNonUpper := false;
  
  var keySeq := seq(|dict.Keys|, i requires 0 <= i < |dict.Keys| => var keys := dict.Keys; var keysList := SetToSeq(keys); keysList[i]);
  
  for k := 0 to |keySeq|
    invariant allLower ==> forall i :: 0 <= i < k ==> IsLowerCase(keySeq[i])
    invariant allUpper ==> forall i :: 0 <= i < k ==> IsUpperCase(keySeq[i])
    invariant hasNonLower ==> exists i :: 0 <= i < k && !IsLowerCase(keySeq[i])
    invariant hasNonUpper ==> exists i :: 0 <= i < k && !IsUpperCase(keySeq[i])
    invariant !allLower ==> hasNonLower
    invariant !allUpper ==> hasNonUpper
    invariant forall key :: key in dict <==> key in keySeq
  {
    var key := keySeq[k];
    if !IsLowerCase(key) {
      allLower := false;
      hasNonLower := true;
    }
    if !IsUpperCase(key) {
      allUpper := false;
      hasNonUpper := true;
    }
  }
  
  if hasNonLower {
    ExistsNotLowerCaseHelper(dict, keySeq);
  }
  if hasNonUpper {
    ExistsNotUpperCaseHelper(dict, keySeq);
  }
  
  result := allLower || allUpper;
}
// </vc-code>

