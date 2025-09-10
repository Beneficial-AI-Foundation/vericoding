predicate ValidInput(n: int, s: string)
{
    n == |s| && n >= 0
}

predicate IsGoodString(s: string)
{
    |s| % 2 == 0 && forall i :: 0 <= i < |s|/2 ==> s[2*i] != s[2*i+1]
}

// <vc-helpers>
function IsGoodStringInternal(s: string, start: int, end: int): bool
  requires 0 <= start <= end <= |s|
  decreases end - start
{
  if start == end then
    true
  else if start + 1 == end then
    true
  else if s[start] != s[start + 1] then
    IsGoodStringInternal(s, start + 2, end)
  else
    false
}

lemma IsGoodString_IsGoodStringInternal(s: string)
  ensures IsGoodString(s) <==> (s.Length % 2 == 0 && IsGoodStringInternal(s, 0, s.Length))
{
  if s.Length % 2 != 0 {
    assert !IsGoodString(s);
    assert !(s.Length % 2 == 0 && IsGoodStringInternal(s, 0, s.Length));
    return;
  }
  if s.Length == 0 {
    assert IsGoodString(s);
    assert s.Length % 2 == 0 && IsGoodStringInternal(s, 0, s.Length);
    return;
  }

  // Prove IsGoodString(s) ==> (s.Length % 2 == 0 && IsGoodStringInternal(s, 0, s.Length))
  if IsGoodString(s) {
    var N := s.Length / 2;
    if N == 0 {
      assert s.Length == 0;
      assert IsGoodStringInternal(s, 0, 0); // IsGoodStringInternal always true for empty range
    } else {
      assert forall i :: 0 <= i < N ==> s[2*i] != s[2*i+1];
      Ghost_IsGoodStringInternal_implies_IsGoodString(s, 0, N*2);
    }
  }

  // Prove (s.Length % 2 == 0 && IsGoodStringInternal(s, 0, s.Length)) ==> IsGoodString(s)
  if s.Length % 2 == 0 && IsGoodStringInternal(s, 0, s.Length) {
    Ghost_IsGoodString_implies_IsGoodStringInternal(s, 0, s.Length);
  }
}

lemma Ghost_IsGoodStringInternal_implies_IsGoodString(s: string, start: int, end: int)
  requires 0 <= start <= end <= |s|
  requires (end-start) % 2 == 0
  requires IsGoodStringInternal(s, start, end)
  ensures forall i :: 0 <= i < (end-start)/2 ==> s[start + 2*i] != s[start + 2*i + 1]
  decreases end - start
{
  if start + 2 <= end {
    assert s[start] != s[start+1];
    Ghost_IsGoodStringInternal_implies_IsGoodString(s, start + 2, end);
  }
}

lemma Ghost_IsGoodString_implies_IsGoodStringInternal(s: string, start: int, end: int)
  requires 0 <= start <= end <= |s|
  requires (end-start) % 2 == 0
  requires forall i :: 0 <= i < (end-start)/2 ==> s[start + 2*i] != s[start + 2*i + 1]
  ensures IsGoodStringInternal(s, start, end)
  decreases end - start
{
  if start + 2 <= end {
    assert s[start] != s[start+1];
    Ghost_IsGoodString_implies_IsGoodStringInternal(s, start + 2, end);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (deletedCount: int, result: string)
    requires ValidInput(n, s)
    ensures deletedCount >= 0
    ensures deletedCount == |s| - |result|
    ensures IsGoodString(result)
    ensures deletedCount + |result| == |s|
// </vc-spec>
// <vc-code>
{
    var deletedChars := 0;
    var resString := "";
    var i := 0;
    while i + 1 < n
        invariant 0 <= i <= n
        invariant 0 <= deletedChars <= i
        invariant deletedChars + |resString| == i
        invariant IsGoodString(resString)
    {
        if s[i] != s[i + 1] {
            var oldResStringLength := |resString>;
            resString := resString + s[i] + s[i + 1];
            i := i + 2;
            Ghost_IsGoodString_implies_IsGoodStringInternal(resString[..oldResStringLength], 0, oldResStringLength);
            Ghost_IsGoodStringInternal_implies_IsGoodString(resString[..oldResStringLength], 0, oldResStringLength);
            assert s[i-2] != s[i-1];
            Ghost_IsGoodString_implies_IsGoodStringInternal(resString, 0, |resString|);
        } else {
            deletedChars := deletedChars + 2;
            i := i + 2;
        }
    }
    deletedCount := deletedChars;
    result := resString;
    assert deletedCount + |result| == i;
    // The loop invariant `deletedChars + |resString| == i` holds.
    // At the end of the loop, `i` is either `n` or `n-1`.
    // If `n` is even, `i` will be `n`. If `n` is odd, `i` will be `n-1`.
    // In the given problem, the `ValidInput` predicate states `n == |s|`,
    // and `IsGoodString` predicate in postcondition requires `|result|` to be even.
    // If n is odd, a character is left over, if n is even, all characters are processed.
    assert i <= n;
    // When the loop terminates, i >= n-1.
    // We need to prove that n-i is either 0 or 1.
    // If n is odd and i = n-1, then there's one character left, which is not included in result.
    // deletedChars + |result| = i implies deletedChars + |result| <= n.
    // If n is even, i must be n. Then deletedChars + |result| = n.
    // If n is odd, i must be n-1. Then deletedChars + |result| = n-1. The last character of s is removed.
    if n % 2 == 1 && i == n - 1 {
      deletedCount := deletedCount + 1; // The last character is discarded
    }
    assert deletedCount + |result| == n;
    assert deletedCount == |s| - |result|;
    assert |result| % 2 == 0; // This must be true for IsGoodString(result)
    assert IsGoodString(result);
}
// </vc-code>

