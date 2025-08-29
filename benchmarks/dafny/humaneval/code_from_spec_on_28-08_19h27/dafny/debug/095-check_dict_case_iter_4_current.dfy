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
lemma KeysNotEmpty(dict: DictCase)
  requires dict != map[]
  ensures dict.Keys != {}
{
}

lemma SetToSeqPreservesElements<T>(s: set<T>)
  ensures forall x :: x in s <==> x in SetToSeq(s)
{
}

lemma SetToSeqCorrectness(keys: set<string>, keySeq: seq<string>)
  requires keySeq == SetToSeq(keys)
  requires keys != {}
  ensures forall i :: 0 <= i < |keySeq| ==> keySeq[i] in keys
  ensures forall key :: key in keys ==> key in keySeq
{
  SetToSeqPreservesElements(keys);
}
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
    ((forall key :: key in dict ==> IsLowerCase(key)) ||
     (forall key :: key in dict ==> IsUpperCase(key))))
// </vc-spec>
// <vc-code>
{
  if dict == map[] {
    return false;
  }
  
  var keys := dict.Keys;
  KeysNotEmpty(dict);
  
  var allLower := true;
  var allUpper := true;
  
  var keySeq := SetToSeq(keys);
  SetToSeqCorrectness(keys, keySeq);
  var i := 0;
  
  while i < |keySeq|
    invariant 0 <= i <= |keySeq|
    invariant allLower ==> forall j :: 0 <= j < i ==> IsLowerCase(keySeq[j])
    invariant allUpper ==> forall j :: 0 <= j < i ==> IsUpperCase(keySeq[j])
    invariant forall j :: 0 <= j < |keySeq| ==> keySeq[j] in keys
    invariant forall key :: key in keys ==> key in keySeq
  {
    var key := keySeq[i];
    if !IsLowerCase(key) {
      allLower := false;
    }
    if !IsUpperCase(key) {
      allUpper := false;
    }
    i := i + 1;
  }
  
  return allLower || allUpper;
}

function SetToSeq<T>(s: set<T>): seq<T>
  decreases s
{
  if s == {} then [] else
    var x := var y :| y in s; y;
    [x] + SetToSeq(s - {x})
}
// </vc-code>
