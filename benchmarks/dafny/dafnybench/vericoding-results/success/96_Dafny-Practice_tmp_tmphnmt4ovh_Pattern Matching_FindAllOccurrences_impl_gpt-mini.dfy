

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method FindAllOccurrences(text: string, pattern: string) returns (offsets: set<nat>)
  ensures forall i:nat :: i in offsets ==> i + |pattern| <= |text|
  ensures forall i:nat :: 0 <= i <= |text| - |pattern|
                       ==> (text[i..i+|pattern|] == pattern <==> i in offsets)
// </vc-spec>
// <vc-code>
{
  var s: set<nat> := {};
  if |pattern| <= |text| {
    var max := |text| - |pattern|;
    var i: nat := 0;
    while i <= max
      invariant i <= max + 1
      invariant forall j: nat :: j < i ==> (j in s <==> text[j..j+|pattern|] == pattern)
      invariant forall k: nat :: k in s ==> k < i
      invariant forall k: nat :: k in s ==> k + |pattern| <= |text|
    {
      var matches := text[i..i+|pattern|] == pattern;
      if matches {
        s := s + {i};
        assert i in s;
      } else {
        // from invariant forall k in s :: k < i we get i not in s
        assert forall k: nat :: k in s ==> k < i;
        assert !(i in s);
      }
      // establish the quantified invariant for j < i+1 (i.e., for the new i after increment)
      assert matches ==> (i in s);
      assert (!matches) ==> !(i in s);
      assert forall j: nat :: j < i + 1 ==> (j in s <==> text[j..j+|pattern|] == pattern);
      i := i + 1;
    }
  }
  offsets := s;
}
// </vc-code>

