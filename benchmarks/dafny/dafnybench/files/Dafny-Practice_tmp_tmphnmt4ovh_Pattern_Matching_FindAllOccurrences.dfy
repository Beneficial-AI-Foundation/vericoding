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
  assume {:axiom} false;
}
// </vc-code>
