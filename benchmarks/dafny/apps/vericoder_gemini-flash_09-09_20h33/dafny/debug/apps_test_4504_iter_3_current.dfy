predicate IsEvenString(s: string)
{
    |s| >= 2 && |s| % 2 == 0 && s[..|s|/2] == s[|s|/2..]
}

predicate ValidInput(S: string)
{
    |S| >= 2 && IsEvenString(S)
}

predicate ValidSolution(S: string, result: int)
{
    2 <= result < |S| && result % 2 == 0 && IsEvenString(S[..result])
}

predicate IsMaximalSolution(S: string, result: int)
{
    ValidSolution(S, result) && 
    forall k :: result < k < |S| && k % 2 == 0 ==> !IsEvenString(S[..k])
}

// <vc-helpers>
function IsEvenStringLen(len: int) : bool
{
  len >= 2 && len % 2 == 0
}
// </vc-helpers>

// <vc-spec>
method solve(S: string) returns (result: int)
    requires ValidInput(S)
    requires exists k :: ValidSolution(S, k)
    ensures ValidSolution(S, result)
    ensures IsMaximalSolution(S, result)
// </vc-spec>
// <vc-code>
{
    var maxLen := 0;
    var Slen := |S|;

    // Loop invariant:
    // 1. maxLen is always an even number.
    // 2. 0 <= maxLen <= Slen.
    // 3. For any even k such that 2 <= k <= maxLen, S[..k] is an even string.
    // 4. For any even k such that maxLen < k < Slen and k % 2 == 0, S[..k] is NOT an even string.
    // 5. This loop finds the maximal length `maxLen` such that S[..maxLen] is an even string.
    for k := 2 to Slen
        invariant 0 <= maxLen <= Slen
        invariant maxLen % 2 == 0
        invariant forall l :: (2 <= l <= maxLen && l % 2 == 0) ==> IsEvenString(S[..l])
        invariant forall l :: (maxLen < l < k && l % 2 == 0) ==> !IsEvenString(S[..l])
        invariant k % 2 == 0
    {
        if IsEvenString(S[..k]) {
            maxLen := k;
        }
    }
    result := maxLen;
}
// </vc-code>

