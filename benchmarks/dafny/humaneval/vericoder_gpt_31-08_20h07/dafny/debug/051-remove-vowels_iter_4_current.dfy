

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

lemma IndexInString(s: string, i: int)
  requires 0 <= i < |s|
  ensures s[i] in s
{
  var k :| 0 <= k < |s| && s[k] == s[i];
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

      // Facts about oldR inherited from invariants (since oldR == r here)
      assert oldR == r;
      assert |oldR| == |r|;
      assert forall k :: 0 <= k < |oldR| ==> !IsVowel(oldR[k]) {
        if 0 <= k < |oldR| {
          assert 0 <= k < |r|;
          assert !IsVowel(r[k]);
          assert oldR[k] == r[k];
        }
      }
      assert forall k :: 0 <= k < |oldR| ==> oldR[k] in text {
        if 0 <= k < |oldR| {
          assert 0 <= k < |r|;
          assert r[k] in text;
          assert oldR[k] == r[k];
        }
      }
      assert forall j0 :: 0 <= j0 < i && !IsVowel(text[j0]) ==> text[j0] in oldR {
        if 0 <= j0 < i {
          // from loop invariant and oldR == r
          assert oldR == r;
        }
      }

      r := oldR + text[i..i+1];

      // Maintain: no vowels in r
      assert forall k :: 0 <= k < |r| ==> !IsVowel(r[k]) {
        if k < |oldR| {
          assert 0 <= k < |oldR|;
          assert r[k] == oldR[k];
          assert !IsVowel(oldR[k]);
        } else {
          assert k == |r| - 1;
          assert r[k] == text[i];
          assert !IsVowel(text[i]);
        }
      }

      // Maintain: every char in r comes from text
      assert forall k :: 0 <= k < |r| ==> r[k] in text {
        if k < |oldR| {
          assert 0 <= k < |oldR|;
          assert r[k] == oldR[k];
          assert oldR[k] in text;
        } else {
          assert k == |r| - 1;
          assert r[k] == text[i];
          assert 0 <= i < |text|;
          IndexInString(text, i);
          assert text[i] in text;
        }
      }

      // Maintain: all prior and current non-vowels from text are in r
      assert forall j0 :: 0 <= j0 < i + 1 && !IsVowel(text[j0]) ==> text[j0] in r {
        if j0 < i {
          assert text[j0] in oldR;
          InStringConcatLeft(text[j0], oldR, text[i..i+1]);
          assert text[j0] in r;
        } else {
          assert j0 == i;
          assert !IsVowel(text[i]);
          assert |r| == |oldR| + 1;
          assert r[|r| - 1] == text[i];
          assert 0 <= |r| - 1 < |r|;
          assert text[i] in r;
        }
      }
    }
    i := i + 1;
  }
  s := r
// </vc-code>

