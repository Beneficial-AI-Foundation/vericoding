// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindAllOccurrences(text: string, pattern: string) returns (offsets: set<nat>)
  ensures forall i:nat :: i in offsets ==> i + |pattern| <= |text|
  ensures forall i:nat :: 0 <= i <= |text| - |pattern|
                       ==> (text[i..i+|pattern|] == pattern <==> i in offsets)
// </vc-spec>
// <vc-code>
{
  offsets := {};
  if |pattern| <= |text| {
    var i: nat := 0;
    while i <= |text| - |pattern|
      invariant 0 <= i <= |text| - |pattern| + 1
      invariant forall k: nat :: k in offsets ==> k < i && text[k..k+|pattern|] == pattern
      invariant forall k: nat :: 0 <= k < i && text[k..k+|pattern|] == pattern ==> k in offsets
    {
      if text[i..i+|pattern|] == pattern {
        offsets := offsets + {i};
      }
      i := i + 1;
    }
  }
}
// </vc-code>
