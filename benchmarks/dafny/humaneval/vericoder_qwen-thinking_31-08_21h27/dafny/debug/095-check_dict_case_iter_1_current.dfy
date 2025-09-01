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
  return (forall k :: k in dict.Keys ==> IsLowerCase(k)) || (forall k :: k in dict.Keys ==> IsUpperCase(k));
}
// </vc-code>

