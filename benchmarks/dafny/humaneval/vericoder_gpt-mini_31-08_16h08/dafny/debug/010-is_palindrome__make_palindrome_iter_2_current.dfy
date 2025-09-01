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
  // Prove palindrome: for all k < 2*n, (s+rev)[k] == (s+rev)[2*n-1-k]
  assert forall k :: 0 <= k < n + n ==>
    (s + rev)[k] == (s + rev)[n + n - 1 - k]
  by {
    fix k;
    if k < n {
      // Left side in s, right side in rev
      assert (s + rev)[k] == s[k];
      var idx := n + n - 1 - k;
      // idx >= n, so (s+rev)[idx] is in rev
      assert idx - n == n - 1 - k;
      assert (s + rev)[idx] == rev[idx - n];
      assert rev[n - 1 - k] == s[k];
      assert (s + rev)[k] == (s + rev)[idx];
    } else {
      // k >= n: left side in rev, right side in s
      var t := k - n;
      assert 0 <= t < n;
      assert (s + rev)[k] == rev[t];
      var idx := n + n - 1 - k;
      // idx < n, so (s+rev)[idx] is in s
      assert idx == n - 1 - t;
      assert (s + rev)[idx] == s[idx];
      assert s[n - 1 - t] == rev[t];
      assert (s + rev)[k] == (s + rev)[idx];
    }
  }
  assert is_palindrome(s + rev);

  // Prove starts_with(s+rev, s)
  assert |s + rev| >= n;
  assert forall i :: 0 <= i < n ==> (s + rev)[i] == s[i]
  by {
    fix i;
    assert (s + rev)[i] == s[i];
  }
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