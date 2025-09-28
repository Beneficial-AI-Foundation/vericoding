// <vc-preamble>
function IsLowerCase(s: string) : bool
{
  forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}
function IsUpperCase(s: string) : bool
{
  forall i :: 0 <= i < |s| ==> 'A' <= s[i] <= 'Z'
}
type DictCase = map<string, string>
// </vc-preamble>

// <vc-helpers>
function AllLowerKeys(dict: DictCase): bool
{
  forall k :: k in dict ==> IsLowerCase(k)
}

function AllUpperKeys(dict: DictCase): bool
{
  forall k :: k in dict ==> IsUpperCase(k)
}
// </vc-helpers>

// <vc-spec>
method CheckDictCase(dict: DictCase) returns (result: bool)

  ensures dict == map[] ==> !result
  ensures result ==> (forall k :: k in dict ==> IsLowerCase(k)) || (forall k :: k in dict ==> IsUpperCase(k))
  ensures !result ==> dict == map[] || ((exists k :: k in dict && !IsLowerCase(k)) && (exists k :: k in dict && !IsUpperCase(k)))
// </vc-spec>
// <vc-code>
{
  if dict == map[] {
    result := false;
  } else {
    var allLower := AllLowerKeys(dict);
    var allUpper := AllUpperKeys(dict);
    result := allLower || allUpper;
    if !result {
      assert !allLower && !allUpper;
      assert exists k :: k in dict && !IsLowerCase(k);
      assert exists k :: k in dict && !IsUpperCase(k);
    }
  }
}
// </vc-code>
