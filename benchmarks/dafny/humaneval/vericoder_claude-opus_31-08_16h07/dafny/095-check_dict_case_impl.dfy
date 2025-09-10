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
    return false;
  }
  
  var allLower := true;
  var allUpper := true;
  
  var keys := dict.Keys;
  
  while keys != {}
    invariant forall k :: k in dict.Keys && k !in keys ==> (allLower ==> IsLowerCase(k)) && (allUpper ==> IsUpperCase(k))
    invariant allLower ==> forall k :: k in dict.Keys && k !in keys ==> IsLowerCase(k)
    invariant allUpper ==> forall k :: k in dict.Keys && k !in keys ==> IsUpperCase(k)
    invariant !allLower ==> exists k :: k in dict.Keys && !IsLowerCase(k)
    invariant !allUpper ==> exists k :: k in dict.Keys && !IsUpperCase(k)
  {
    var k :| k in keys;
    
    if !IsLowerCase(k) {
      allLower := false;
    }
    if !IsUpperCase(k) {
      allUpper := false;
    }
    
    keys := keys - {k};
  }
  
  result := allLower || allUpper;
}
// </vc-code>

