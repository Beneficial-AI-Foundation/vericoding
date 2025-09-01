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
lemma ValidateEmptyDictCheck(dict: DictCase)
  ensures dict == map[] ==> (forall k :: k in dict ==> IsLowerCase(k)) == true
  ensures dict == map[] ==> (forall k :: k in dict ==> IsUpperCase(k)) == true
{}
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
  if dict == map[] then
    return false;
  
  ValidateEmptyDictCheck(dict);

  var allLower := true;
  var allUpper := true;

  for k in dict.Keys {
    if !IsLowerCase(k) {
      allLower := false;
    }
    if !IsUpperCase(k) {
      allUpper := false;
    }
  }
  return allLower || allUpper;
}
// </vc-code>

