function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}

// <vc-helpers>
lemma PalindromeFromMirror(s: string, t: string)
  requires |t| == |s|
  requires forall k :: 0 <= k < |s| ==> t[k] == s[|s| - 1 - k]
  ensures is_palindrome(s + t)
{
  assert |s + t| == |s| + |t|;
  forall k | 0 <= k < |s| + |t|
    ensures (s + t)[k] == (s + t)[|s| + |t| - 1 - k]
  {
    if k < |s| {
      assert (s + t)[k] == s[k];
      var m := |s| + |t| - 1 - k;
      assert m < |s| + |t|;
      assert |t| == |s|;
      assert m >= |s|;
      assert (s + t)[m] == t[m - |s|];
      assert m - |s| == |t| - 1 - k;
      assert |t| - 1 - k >= 0;
      assert |t| - 1 - k < |t|;
      assert t[|t| - 1 - k] == s[|s| - 1 - (|t| - 1 - k)];
      assert |t| == |s|;
      assert s[|s| - 1 - (|s| - 1 - k)] == s[k];
    } else {
      var p := k - |s|;
      assert 0 <= p && p < |t|;
      assert (s + t)[k] == t[p];
      var m := |s| + |t| - 1 - k;
      assert m >= 0;
      assert |t| == |s|;
      assert m < |s|;
      assert (s + t)[m] == s[m];
      assert m == |s| - 1 - p;
      assert 0 <= p && p < |s|;
      assert t[p] == s[|s| - 1 - p];
    }
  }
}

lemma StartsWithConcatLeft(s: string, t: string)
  ensures starts_with(s + t, s)
{
  assert |s + t| >= |s|;
  assert forall k :: 0 <= k < |s| ==> (s + t)[k] == s[k];
}
// </vc-helpers>

// <vc-spec>
method make_palindrome(s: string) returns (result: string)
    // post-conditions-start
    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var t := reverse(s);
  result := s + t;
  assert |t| == |s|;
  assert |result| == |s| + |t|;
  assert |result| == 2 * |s|;
  PalindromeFromMirror(s, t);
  StartsWithConcatLeft(s, t);
}
// </vc-code>

method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
{
  assume{:axiom} false;
}