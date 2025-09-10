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
    true // This case should ideally not be reached if (end-start) is even.
         // If (end-start) is odd, IsGoodString would be false.
         // However, for single character strings, it's considered good.
  else if s[start] != s[start + 1] then
    IsGoodStringInternal(s, start + 2, end)
  else
    false
}

lemma IsGoodString_IsGoodStringInternal(s: string)
  ensures IsGoodString(s) <==> (s.Length % 2 == 0 && IsGoodStringInternal(s, 0, s.Length))
{
  if s.Length % 2 != 0 {
    assert !IsGoodString(s); // IsGoodString requires length to be even
    assert !(s.Length % 2 == 0 && IsGoodStringInternal(s, 0, s.Length));
    return;
  }
  if s.Length == 0 {
    assert IsGoodString(s);
    assert s.Length % 2 == 0 && IsGoodStringInternal(s, 0, 0);
    return;
  }

  // Prove IsGoodString(s) ==> (s.Length % 2 == 0 && IsGoodStringInternal(s, 0, s.Length))
  if IsGoodString(s) {
    if s.Length % 2 == 0 { // This is already guaranteed by IsGoodString(s)
       Ghost_IsGoodString_implies_IsGoodStringInternal(s, 0, s.Length);
    }
  }

  // Prove (s.Length % 2 == 0 && IsGoodStringInternal(s, 0, s.Length)) ==> IsGoodString(s)
  if s.Length % 2 == 0 && IsGoodStringInternal(s, 0, s.Length) {
    Ghost_IsGoodStringInternal_implies_IsGoodString(s, 0, s.Length);
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
    assert s[start] != s[start+1]; // This is true by definition of IsGoodStringInternal
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
    assert s[start] != s[start+1]; // This is true by the precondition
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
            var oldResStringLength := |resString|;
            resString := resString + s[i] + s[i + 1];
            Ghost_IsGoodString_implies_IsGoodStringInternal(resString[..oldResStringLength], 0, oldResStringLength);
            Ghost_IsGoodStringInternal_implies_IsGoodString(resString[..oldResStringLength], 0, oldResStringLength);
            assert forall k :: 0 <= k < oldResStringLength/2 ==> resString[2*k] != resString[2*k+1];
            assert s[i] != s[i+1];

            // Prove that the new resString is good.
            // Since resString[..oldResStringLength] is good, we need to show the new pair is good and it combines well.
            // Let old_len = oldResStringLength.
            // We know resString[0..old_len-1] is good.
            // We append s[i]s[i+1]. We know s[i] != s[i+1].
            // To show IsGoodString(resString), we need to show:
            // 1. |resString| is even (true, old_len is even, we add 2 chars)
            // 2. For all pairs, chars are different.
            // For pairs in old part, they are already different.
            // For the new pair, s[i] != s[i+1] which is the `if` condition.
            if oldResStringLength > 0 {
              Ghost_IsGoodString_implies_IsGoodStringInternal(resString, 0, oldResStringLength);
              Ghost_IsGoodStringInternal_implies_IsGoodString(resString, 0, oldResStringLength);
            }
            Ghost_IsGoodString_implies_IsGoodStringInternal(resString, 0, |resString|);
            i := i + 2;


        } else {
            deletedChars := deletedChars + 2;
            i := i + 2;
        }
    }
    deletedCount := deletedChars;
    result := resString;
    assert deletedCount + |result| == i;

    if n % 2 == 1 && i == n - 1 {
      deletedCount := deletedCount + 1; // The last character is discarded
    }
    assert deletedCount + |result| == n;
    assert deletedCount == |s| - |result|;
    assert |result| % 2 == 0;
    assert IsGoodString(result);
}
// </vc-code>

