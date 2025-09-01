

// <vc-helpers>
function IsVowel(c: char): bool
{
  c == 'a' || c == 'e' || c == 'i' || c == 'o' || c == 'u'
}

lemma InStringConcatLeft(x: char, s: string, t: string)
  ensures x in s ==> x in s + t
{
  if x in s {
    var k :| 0 <= k < |s| && s[k] == x;
    assert 0 <= k < |s + t|;
    assert (s + t)[k] == x;
  }
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
    decreases |text| - i
  {
    if !IsVowel(text[i]) {
      var oldR := r;
      r := oldR + text[i..i+1];

      assert 0 <= i < |text|;
      assert |r| == |oldR| + 1;
      assert r[|r| - 1] == text[i];

      assert forall k :: 0 <= k < |r| ==> !IsVowel(r[k]) {
        if k < |oldR| {
          assert 0 <= k < |oldR|;
          assert r[k] == oldR[k];
        } else {
          assert k == |r| - 1;
          assert r[k] == text[i];
        }
      }

      assert text[i] in text;
      assert forall k :: 0 <= k < |r| ==> r[k] in text {
        if k < |oldR| {
          assert 0 <= k < |oldR|;
          assert oldR[k] in text;
          assert r[k] == oldR[k];
        } else {
          assert k == |r| - 1;
          assert r[k] == text[i];
        }
      }

      assert forall j0 :: 0 <= j0 < i + 1 && !IsVowel(text[j0]) ==> text[j0] in r {
        if j0 < i {
          assert 0 <= j0 < i;
          assert !IsVowel(text[j0]) ==> text[j0] in oldR;
          if !IsVowel(text[j0]) {
            InStringConcatLeft(text[j0], oldR, text[i..i+1]);
          }
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

