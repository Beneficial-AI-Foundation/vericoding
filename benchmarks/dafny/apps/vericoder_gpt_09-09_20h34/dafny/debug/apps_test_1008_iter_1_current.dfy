function isPalindrome(s: string): bool
{
    forall i :: 0 <= i < |s| / 2 ==> s[i] == s[|s| - 1 - i]
}

// <vc-helpers>
lemma MulMonoLe(a: int, b: int, c: int)
  requires a <= b
  requires 0 <= c
  ensures a * c <= b * c
  decreases b - a
{
  if a == b {
  } else {
    assert a < b;
    assert a * c <= a * c + c;
    MulMonoLe(a + 1, b, c);
    assert a * c + c == (a + 1) * c;
    assert a * c <= (a + 1) * c;
    assert (a + 1) * c <= b * c;
    assert a * c <= b * c;
  }
}
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
{
  if |s| % k != 0 {
    result := "NO";
    return;
  }
  var n := |s|;
  var chunk := n / k;
  assert n % k == 0;
  assert n == chunk * k;
  assert 0 <= chunk;
  var i := 0;
  while i <
// </vc-code>

