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
lemma ExistsLowerAndUpper(dict: DictCase)
  requires dict != map[]
  requires exists k :: k in dict && !IsLowerCase(k)
  requires exists k :: k in dict && !IsUpperCase(k)
{
}

lemma NotAllSameCase(dict: DictCase)
  ensures (exists k :: k in dict && !IsLowerCase(k)) ==> !(forall k :: k in dict ==> IsLowerCase(k))
  ensures (exists k :: k in dict && !IsUpperCase(k)) ==> !(forall k :: k in dict ==> IsUpperCase(k))
{
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
  } else {
    var hasLower: bool := true;
    var hasUpper: bool := true;
    
    var keys := dict.Keys;
    
    foreach (key in keys) {
      if !IsLowerCase(key) {
        hasLower := false;
      }
      if !IsUpperCase(key) {
        hasUpper := false;
      }
    }
    
    result := hasLower || hasUpper;
  }
}
// </vc-code>

