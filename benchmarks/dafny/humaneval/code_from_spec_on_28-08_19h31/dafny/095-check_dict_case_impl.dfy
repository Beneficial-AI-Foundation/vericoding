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
lemma NonEmptyDictHasKey(dict: DictCase)
  ensures dict != map[] ==> exists k :: k in dict
{
  if dict != map[] {
    var k :| k in dict;
    assert k in dict;
  }
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
method CheckDictCaseImpl(dict: DictCase) returns (result: bool)
{
  if dict == map[] {
    return false;
  }
  
  var allLower := true;
  var allUpper := true;
  
  var keys := dict.Keys;
  var keyIter := keys;
  while keyIter != {}
    decreases |keyIter|
  {
    var k :| k in keyIter;
    if !IsLowerCase(k) {
      allLower := false;
    }
    if !IsUpperCase(k) {
      allUpper := false;
    }
    keyIter := keyIter - {k};
  }
  
  result := allLower || allUpper;
}
// </vc-code>
