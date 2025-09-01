```vc-helpers
lemma palindrome_of_concat_with_reverse(s: string, rev: string)
  requires |rev| == |s|
  requires forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  ensures is_palindrome(s + rev)
{
  assert forall k:int :: 0 <= k < |s| + |rev| ==> (s + rev)[k] == (s + rev)[|s| + |rev| - 1 - k] {
    assume 0 <= k < |s| + |rev|;
    if k < |s| {
      var j := |s| + |rev| - 1 - k;
      assert j >= |s|;
      assert j - |s| == |rev| - 1 - k;
      assert |rev| == |s|;
      assert j - |s| == |s| - 1 - k;
      assert (s + rev)[k] == s[k];
      assert (s + rev)[j] == rev[j - |s|];
      assert rev[|s| - 1 - k] == s[k];
    } else {
      var i := k - |s|;
      assert 0 <= i;
      assert i < |rev|;
      assert (s + rev)[k] == rev[i];
      assert rev[i] == s[|s| - 1 - i];
      var j2 := |s| + |rev| - 1 - k;
      assert j2 == |s| + |s| - 1 - k; // using |rev| == |s|
      assert j2 == |s| - 1 - i;
      assert j2 < |s|;
      assert (s + rev)[j2] == s[j2];
      assert s[|s| - 1 - i] == s[j2];
    }
  }
}
```

```vc-code
{
  var rev := reverse(s);
  result := s + rev;

  // length bound
  assert |rev| == |s|;
  assert |result| == |s| + |rev|;
  assert |result| <= 2 * |s|;

  // starts_with(result, s)
  assert |result| >= |s|;
  assert forall k:int :: 0 <= k < |s| ==> result[k] == s[k];

  // palindrome
  palindrome_of_concat_with_reverse(s, rev);
}
```