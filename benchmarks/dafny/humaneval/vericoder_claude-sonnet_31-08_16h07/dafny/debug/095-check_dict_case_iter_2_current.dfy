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

lemma ExistsNotLowerCaseHelper(dict: DictCase)
  requires exists k :: k in dict && !IsLowerCase(k)
  ensures !(forall k :: k in dict ==> IsLowerCase(k))

lemma ExistsNotUpperCaseHelper(dict: DictCase)
  requires exists k :: k in dict && !IsUpperCase(k)
  ensures !(forall k :: k in dict ==> IsUpperCase(k))
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
  
  var keys := dict.Keys;
  
  for k := 0 to |keys|
    invariant allLower ==> forall i :: 0 <= i < k ==> IsLowerCase(keys[i])
    invariant allUpper ==> forall i :: 0 <= i < k ==> IsUpperCase(keys[i])
    invariant hasNonLower ==> exists i :: 0 <= i < k && !IsLowerCase(keys[i])
    invariant hasNonUpper ==> exists i :: 0 <= i < k && !IsUpperCase(keys[i])
    invariant !allLower ==> hasNonLower
    invariant !allUpper ==> hasNonUpper
  {
    var key := keys[k];
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
    ExistsNotLowerCaseHelper(dict);
  }
  if hasNonUpper {
    ExistsNotUpperCaseHelper(dict);
  }
  
  result := allLower || allUpper;
}
// </vc-code>

