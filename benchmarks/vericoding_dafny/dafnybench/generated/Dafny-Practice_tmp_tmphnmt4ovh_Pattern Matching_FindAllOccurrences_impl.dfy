method FindAllOccurrences(text: string, pattern: string) returns (offsets: set<nat>)
  ensures forall i:nat :: i in offsets ==> i + |pattern| <= |text|
  ensures forall i:nat :: 0 <= i <= |text| - |pattern|
                       ==> (text[i..i+|pattern|] == pattern <==> i in offsets)
// </vc-spec>
// <vc-code>
{
  offsets := {};
  
  if |pattern| == 0 {
    // When pattern is empty, it matches at every position
    var j := 0;
    while j <= |text|
      invariant 0 <= j <= |text| + 1
      invariant forall k:nat :: 0 <= k < j ==> k in offsets
      invariant forall k:nat :: k in offsets ==> 0 <= k <= |text|
    {
      offsets := offsets + {j};
      j := j + 1;
    }
    return;
  }
  
  if |pattern| > |text| {
    return;
  }
  
  var i := 0;
  while i <= |text| - |pattern|
    invariant 0 <= i <= |text| - |pattern| + 1
    invariant forall j:nat :: j in offsets ==> j + |pattern| <= |text|
    invariant forall j:nat :: j in offsets ==> 0 <= j < i
    invariant forall j:nat :: 0 <= j < i ==> (text[j..j+|pattern|] == pattern <==> j in offsets)
  {
    if text[i..i+|pattern|] == pattern {
      offsets := offsets + {i};
    }
    i := i + 1;
  }
}
// </vc-code>