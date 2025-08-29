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
// </vc-helpers>

// <vc-description>
/*
function_signature: def check_dict_case(s : dict[str, str]) -> bool
Given a dictionary, return True if all keys are strings in lower case or all keys are strings in upper case, else return False. The function should return False is the given dictionary is empty. Note(George): Modified the problem to use strings only for both keys and values.
*/
// </vc-description>

// <vc-spec>
method CheckDictCase(dict: DictCase) returns (result: bool)
  ensures result == (dict != map[] && 
    (forall key :: key in dict ==> IsLowerCase(key)) ||
    (forall key :: key in dict ==> IsUpperCase(key)))
// </vc-spec>
// <vc-code>
{
  if dict == map[] {
    return false;
  }
  
  var keys := dict.Keys;
  if keys == {} {
    return false;
  }
  
  var allLower := true;
  var allUpper := true;
  
  for key in keys {
    if !IsLowerCase(key) {
      allLower := false;
    }
    if !IsUpperCase(key) {
      allUpper := false;
    }
  }
  
  return allLower || allUpper;
}
// </vc-code>
