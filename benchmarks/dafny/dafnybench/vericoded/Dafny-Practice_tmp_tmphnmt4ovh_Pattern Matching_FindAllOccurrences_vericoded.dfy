

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
  
  if |pattern| == 0 {
    // Empty pattern matches at every position including |text|
    var i := 0;
    while i <= |text|
      invariant 0 <= i <= |text| + 1
      invariant offsets == (set j {:trigger j in offsets} | 0 <= j < i :: j)
    {
      offsets := offsets + {i};
      i := i + 1;
    }
    return;
  }
  
  if |pattern| > |text| {
    // Pattern is longer than text, no matches possible
    return;
  }
  
  var i := 0;
  while i <= |text| - |pattern|
    invariant 0 <= i <= |text| - |pattern| + 1
    invariant forall j:nat :: j in offsets ==> j + |pattern| <= |text|
    invariant forall j:nat :: j in offsets ==> j < i
    invariant forall j:nat :: 0 <= j < i && j <= |text| - |pattern| ==> 
                              (text[j..j+|pattern|] == pattern <==> j in offsets)
  {
    if text[i..i+|pattern|] == pattern {
      offsets := offsets + {i};
    }
    i := i + 1;
  }
}
// </vc-code>

