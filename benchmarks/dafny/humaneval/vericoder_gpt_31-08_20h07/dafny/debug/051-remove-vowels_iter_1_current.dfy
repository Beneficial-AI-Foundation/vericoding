

// <vc-helpers>
function IsVowel(c: char): bool
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}
// </vc-helpers>

// <vc-spec>
method remove_vowels(text : string) returns (s : string)
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] != 'a' && s[i] != 'e' && s[i] != 'i' && s[i] != 'o' && s[i] != 'u'
    ensures forall i : int :: i >= 0 && i < |s| ==> s[i] in text
    ensures forall j : int :: j >= 0 && j < |text| && text[j] != 'a' && text[j] != 'e' && text[j] != 'i' && text[j] != 'o' && text[j] != 'u' ==> text[j] in s
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var r := "";
  var i := 0;
  while i < |text|
    invariant 0 <= i <= |text|
    invariant forall k :: 0 <= k < |r| ==> !IsVowel(r[k])
    invariant forall k :: 0 <= k < |r| ==> r[k] in text
    invariant forall j :: 0 <= j < i && !IsVowel(text[j]) ==> text[j] in r
  {
    if !IsVowel(text[i]) {
      // text[i] is a non-vowel; we will append it
      assert text[i] in text;
      var oldR := r;
      r := oldR + text[i..i+1];
      // Establish invariants for r
      assert |r| == |oldR| + 1;
      assert r[|r| - 1] == text[i];

      // r has no vowels
      assert forall k :: 0 <= k < |r| ==> !IsVowel(r[k]) {
        if k < |oldR| {
          assert r[k] == oldR[k];
        } else {
          assert k == |r| - 1;
        }
      }

      // Every char of r appears in text
      assert forall k :: 0 <= k < |r| ==> r[k] in text {
        if k < |oldR| {
          assert r[k] == oldR[k];
        } else {
          assert k == |r| - 1;
          assert r[k] == text[i];
        }
      }

      // All processed non-vowel chars of text appear in r
      assert forall j0 :: 0 <= j0 < i + 1 && !IsVowel(text[j0]) ==> text[j0] in r {
        if j0 < i {
          // follows from previous invariant and r = oldR + ...
        } else {
          assert j0 == i;
          assert r[|r| - 1] == text[i];
        }
      }
    }
    i := i + 1;
  }
  s := r;
}
// </vc-code>

