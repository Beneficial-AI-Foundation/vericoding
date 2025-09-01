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
  forall k | 0 <= k < |s| + |t|
    ensures (s + t)[k] == (s + t)[|s| + |t| - 1 - k]
  {
    if k < |s| {
      // Left side
      assert (s + t)[k] == s[k];

      // j = |s| - 1 - k is within [0, |t|)
      assert 0 <= |s| - 1 - k;
      assert |s| - 1 - k <= |s| - 1;
      assert |s| - 1 < |s|;
      assert |s| - 1 - k
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
lemma PalindromeFromMirror(s: string, t: string)
  requires |t| == |s|
  requires forall k :: 0 <= k < |s| ==> t[k] == s[|s| - 1 - k]
  ensures is_palindrome(s + t)
{
  forall k | 0 <= k < |s| + |t|
    ensures (s + t)[k] == (s + t)[|s| + |t| - 1 - k]
  {
    if k < |s| {
      // Left side
      assert (s + t)[k] == s[k];

      // j = |s| - 1 - k is within [0, |t|)
      assert 0 <= |s| - 1 - k;
      assert |s| - 1 - k <= |s| - 1;
      assert |s| - 1 < |s|;
      assert |s| - 1 - k
// </vc-code>

method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
{
  assume{:axiom} false;
}