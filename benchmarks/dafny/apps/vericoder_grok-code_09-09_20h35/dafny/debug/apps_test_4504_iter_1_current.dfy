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
  var n := |S|;
  var low := 2;
  var high := n - 2;
  var result := 0;
  while low <= high
    decreases high - low
  {
    var diff := high - low;
    var mid := low + (diff / 4 * 2);
    if IsEvenString(S[..mid]) {
      result := mid;
      low := mid + 2;
    } else {
      high := mid - 2;
    }
  }
  return result;
}
// </vc-code>

