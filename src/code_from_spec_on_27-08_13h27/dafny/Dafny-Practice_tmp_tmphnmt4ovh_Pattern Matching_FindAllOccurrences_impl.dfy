// <vc-helpers>
function IsSubstringAt(text: string, pattern: string, start: nat): bool
  requires start + |pattern| <= |text|
{
  text[start..start + |pattern|] == pattern
}

lemma SubstringCheck(text: string, pattern: string, i: nat)
  requires 0 <= i <= |text| - |pattern|
  ensures IsSubstringAt(text, pattern, i) <==> text[i..i + |pattern|] == pattern
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method FindAllOccurrences(text: string, pattern: string) returns (offsets: set<nat>)
  ensures forall i:nat :: i in offsets ==> i + |pattern| <= |text|
  ensures forall i:nat :: 0 <= i <= |text| - |pattern|
                       ==> (text[i..i+|pattern|] == pattern <==> i in offsets)
// </vc-spec>
// </vc-spec>

// <vc-code>
method FindAllOccurrencesImpl(text: string, pattern: string) returns (offsets: set<nat>)
  ensures forall i:nat :: i in offsets ==> i + |pattern| <= |text|
  ensures forall i:nat :: 0 <= i <= |text| - |pattern|
                       ==> (text[i..i+|pattern|] == pattern <==> i in offsets)
{
  offsets := {};
  if |pattern| == 0 || |text| < |pattern| {
    return;
  }
  
  var i := 0;
  while i <= |text| - |pattern|
    invariant 0 <= i <= |text| - |pattern| + 1
    invariant forall k:nat :: k in offsets ==> k < i && k + |pattern| <= |text|
    invariant forall k:nat :: 0 <= k < i ==> (text[k..k+|pattern|] == pattern <==> k in offsets)
  {
    if text[i..i + |pattern|] == pattern {
      offsets := offsets + {i};
    }
    i := i + 1;
  }
  assert i == |text| - |pattern| + 1;
  assert forall k:nat :: 0 <= k <= |text| - |pattern| ==> (text[k..k+|pattern|] == pattern <==> k in offsets);
}
// </vc-code>
