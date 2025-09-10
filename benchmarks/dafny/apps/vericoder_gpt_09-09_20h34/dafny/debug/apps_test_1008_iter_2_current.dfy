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
  while i < k
    invariant 0 <= i <= k
    invariant n == |s|
    invariant chunk == n / k
    invariant n == chunk * k
    invariant 0 <= chunk
    invariant forall j :: 0 <= j < i ==> isPalindrome(s[j * chunk .. (j + 1) * chunk])
    decreases k - i
  {
    var start := i * chunk;
    var end := (i + 1) * chunk;
    MulMonoLe(0, i, chunk);
    assert 0 <= start;
    MulMonoLe(i, i + 1, chunk);
    assert start <= end;
    MulMonoLe(i + 1, k, chunk);
    assert end <= n;
    if !isPalindrome(s[start .. end]) {
      result := "NO";
      assert 0 <= i < k;
      assert exists j :: 0 <= j < k && !isPalindrome(s[j * chunk .. (j + 1) * chunk]);
      return;
    }
    i := i + 1;
  }
  result := "YES";
}
// </vc-code>

