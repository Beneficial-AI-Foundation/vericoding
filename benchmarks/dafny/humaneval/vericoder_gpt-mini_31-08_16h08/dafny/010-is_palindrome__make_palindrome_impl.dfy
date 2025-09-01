function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}

// <vc-helpers>
lemma concat_palindrome_from_rev(s: string, rev: string)
  requires |rev| == |s|
  requires forall i :: 0 <= i < |s| ==> rev[i] == s[|s|-1-i]
  ensures is_palindrome(s + rev)
  ensures starts_with(s + rev, s)
  ensures |s + rev| <= 2 * |s|
{
  var n := |s|;

  // Prove palindrome by iterating over indices
  var i := 0;
  while i < 2 * n
    invariant 0 <= i <= 2 * n
    invariant forall k :: 0 <= k < i ==> (s + rev)[k] == (s + rev)[2 * n - 1 - k]
  {
    if i < n {
      // left in s, right in rev
      assert 0 <= i < n;
      assert (s + rev)[i] == s[i];
      var idx := 2 * n - 1 - i;
      assert idx >= n;
      assert idx - n == n - 1 - i;
      assert (s + rev)[idx] == rev[idx - n];
      assert rev[n - 1 - i] == s[i];
      assert (s + rev)[i] == (s + rev)[idx];
    } else {
      // left in rev, right in s
      var t := i - n;
      assert 0 <= t < n;
      assert (s + rev)[i] == rev[t];
      var idx := 2 * n - 1 - i;
      assert idx < n;
      assert idx == n - 1 - t;
      assert (s + rev)[idx] == s[idx];
      assert s[n - 1 - t] == rev[t];
      assert (s + rev)[i] == (s + rev)[idx];
    }
    i := i + 1;
  }
  assert forall k :: 0 <= k < 2 * n ==> (s + rev)[k] == (s + rev)[2 * n - 1 - k];
  assert is_palindrome(s + rev);

  // Prove starts_with by iterating over prefix indices
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant forall k :: 0 <= k < j ==> (s + rev)[k] == s[k]
  {
    assert 0 <= j < n;
    assert (s + rev)[j] == s[j];
    j := j + 1;
  }
  assert forall k :: 0 <= k < n ==> (s + rev)[k] == s[k];
  assert starts_with(s + rev, s);

  // Length bound
  assert |s + rev| == |s| + |rev|;
  assert |rev| == n;
  assert |s + rev| == 2 * n;
  assert |s + rev| <= 2 * n;
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
  var rev := reverse(s);
  result := s + rev;
  concat_palindrome_from_rev(s, rev);
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