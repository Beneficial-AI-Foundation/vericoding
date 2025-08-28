function IsLowerCase(s: string) : bool
{
  forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}
// pure-end
function IsUpperCase(s: string) : bool
{
  forall i :: 0 <= i < |s| ==> 'A' <= s[i] <= 'Z'
}
// pure-end
type DictCase = map<string, string>

method CheckDictCase(dict: DictCase) returns (result: bool)
  // post-conditions-start
  ensures dict == map[] ==> !result
  ensures result ==> (forall k :: k in dict ==> IsLowerCase(k)) || (forall k :: k in dict ==> IsUpperCase(k))
  ensures !result ==> dict == map[] || ((exists k :: k in dict && !IsLowerCase(k)) && (exists k :: k in dict && !IsUpperCase(k)))
  // post-conditions-end
{
  // impl-start
  if |dict| == 0 {
    return false;
  }

  var allLower := true;
  var allUpper := true;

  var keys := dict.Keys;
  while keys != {}
    // invariants-start
    invariant allLower ==> forall j :: j in dict.Keys - keys ==> IsLowerCase(j)
    invariant allUpper ==> forall j :: j in dict.Keys - keys ==> IsUpperCase(j)
    invariant !allLower ==> exists j :: j in dict.Keys - keys && !IsLowerCase(j)
    invariant !allUpper ==> exists j :: j in dict.Keys - keys && !IsUpperCase(j)
    // invariants-end
  {
    var k :| k in keys;
    if !IsLowerCase(k) {
      allLower := false;
    }
    if !IsUpperCase(k) {
      allUpper := false;
    }
    if !allLower && !allUpper {
      return false;
    }
    keys := keys - {k};
  }

  result := allLower || allUpper;
  // impl-end
}
