function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

// <vc-helpers>
lemma DivMul(len:int, k:int)
  requires k > 0
  requires len >= 0
  requires len % k == 0
  ensures (len / k) * k == len
{
  assert len == (len / k) * k + len % k;
  assert len % k == 0;
  assert len == (len / k) * k;
}

lemma DivNonneg(len:int, k:int)
  requires k > 0
  requires len >= 0
  ensures len / k >= 0
{
  assert len / k >= 0;
}

lemma DivUnique(len:int, k:int, m:int)
  requires k > 0
  requires len >= 0
  requires m * k == len
  ensures m == len / k
{
  var q := len / k;
  var r := len % k;
  assert len == q * k + r;
  assert 0 <= r < k;
  // (m - q) * k == r
  assert (m - q) * k == len - q * k;
  assert len - q * k == r;
  assert (m - q) * k == r;
  if m - q > 0 {
    // then (m-q)*k >= k > r, contradiction
    assert (m - q) * k >= k;
    assert k > r;
    assert (m - q) * k > r;
    // contradiction with (m-q)*k == r
// </vc-helpers>

// <vc-spec>
method solve(s: string, k: int) returns (result: string)
    requires k > 0
    ensures result == "YES" || result == "NO"
    ensures |s| % k != 0 ==> result == "NO"
    ensures |s| % k == 0 && (forall i :: 0 <= i < k ==> 
        isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "YES"
    ensures |s| % k == 0 && (exists i :: 0 <= i < k && 
        !isPalindrome(s[i * (|s| / k)..(i + 1) * (|s| / k)])) ==> result == "NO"
// </vc-spec>
// <vc-code>
lemma DivMul(len:int, k:int)
  requires k > 0
  requires len >= 0
  requires len % k == 0
  ensures (len / k) * k == len
{
  assert len == (len / k) * k + len % k;
  assert len % k == 0;
  assert len == (len / k) * k;
}

lemma DivNonneg(len:int, k:int)
  requires k > 0
  requires len >= 0
  ensures len / k >= 0
{
  assert len / k >= 0;
}

lemma DivUnique(len:int, k:int, m:int)
  requires k > 0
  requires len >= 0
  requires m * k == len
  ensures m == len / k
{
  var q := len / k;
  var r := len % k;
  assert len == q * k + r;
  assert 0 <= r < k;
  // (m - q) * k == r
  assert (m - q) * k == len - q * k;
  assert len - q * k == r;
  assert (m - q) * k == r;
  if m - q > 0 {
    // then (m-q)*k >= k > r, contradiction
    assert (m - q) * k >= k;
    assert k > r;
    assert (m - q) * k > r;
    // contradiction with (m-q)*k == r
// </vc-code>

