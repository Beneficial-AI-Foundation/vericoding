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
predicate AllLowerKeys(dict: DictCase) { forall k :: k in dict ==> IsLowerCase(k) }
predicate AllUpperKeys(dict: DictCase) { forall k :: k in dict ==> IsUpperCase(k) }
lemma NotAllImpliesExistsLower(dict: DictCase)
  ensures !AllLowerKeys(dict) ==> (exists k :: k in dict && !IsLowerCase(k))
{ }
lemma NotAllImpliesExistsUpper(dict: DictCase)
  ensures !AllUpperKeys(dict) ==> (exists k :: k in dict && !IsUpperCase(k))
{ }
// </vc-helpers>

// <vc-spec>
method CheckDictCase(dict: DictCase) returns (result: bool)

  ensures dict == map[] ==> !result
  ensures result ==> (forall k :: k in dict ==> IsLowerCase(k)) || (forall k :: k in dict ==> IsUpperCase(k))
  ensures !result ==> dict == map[] || ((exists k :: k in dict && !IsLowerCase(k)) && (exists k :: k in dict && !IsUpperCase(k)))
// </vc-spec>
// <vc-code>
{
  var allLower := forall k :: k in dict ==> IsLowerCase(k);
  var allUpper := forall k :: k in dict ==> IsUpperCase(k);
  result := dict != map[] && (allLower || allUpper);
  if !result && dict != map[] {
    assert !allLower;
    assert !allUpper;
    NotAllImpliesExistsLower(dict);
    NotAllImpliesExistsUpper(dict);
    assert exists k :: k in dict && !IsLowerCase(k);
    assert exists k :: k in dict && !IsUpperCase(k);
  }
}
// </vc-code>
