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
function IsLowerCaseStr(s: string) : bool
{
  forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

function IsUpperCaseStr(s: string) : bool
{
  forall i :: 0 <= i < |s| ==> 'A' <= s[i] <= 'Z'
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def check_dict_case(s : dict[str, str]) -> bool
Given a dictionary, return True if all keys are strings in lower case or all keys are strings in upper case, else return False. The function should return False is the given dictionary is empty. Note(George): Modified the problem to use strings only for both keys and values.
*/
// </vc-description>

// <vc-spec>
method CheckDictCase(d: DictCase) returns (result: bool)
  ensures result == (d != map[] && ((forall k :: k in d.Keys ==> IsLowerCaseStr(k)) || (forall k :: k in d.Keys ==> IsUpperCaseStr(k))))
// </vc-spec>
// <vc-code>
{
  if d == map[] {
    return false;
  }
  
  var allLower := true;
  var allUpper := true;
  
  var keysSeq: seq<string> := [];
  var keySet := d.Keys;
  var keyArray := setToSeq(keySet);
  keysSeq := keyArray;
  
  for i := 0 to |keysSeq|
    invariant 0 <= i <= |keysSeq|
    invariant allLower ==> forall j :: 0 <= j < i ==> IsLowerCaseStr(keysSeq[j])
    invariant allUpper ==> forall j :: 0 <= j < i ==> IsUpperCaseStr(keysSeq[j])
  {
    var k := keysSeq[i];
    if !IsLowerCaseStr(k) {
      allLower := false;
    }
    if !IsUpperCaseStr(k) {
      allUpper := false;
    }
    if !allLower && !allUpper {
      return false;
    }
  }
  
  return allLower || allUpper;
}
// </vc-code>
