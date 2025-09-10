predicate ValidInput(s: string)
{
    |s| > 0 && forall i :: 0 <= i < |s| ==> s[i] == 'a' || s[i] == 'b'
}

function MergeConsecutive(s: string): string
    requires |s| > 0
{
    if |s| == 1 then s
    else if s[0] == s[1] then MergeConsecutive(s[1..])
    else [s[0]] + MergeConsecutive(s[1..])
}

function IsPalindrome(s: string): bool
{
    if |s| <= 1 then true
    else s[0] == s[|s|-1] && IsPalindrome(s[1..|s|-1])
}

predicate IsGoodSubstring(s: string, i: int, j: int)
    requires ValidInput(s) && 0 <= i <= j < |s|
{
    var sub := s[i..j+1];
    IsPalindrome(MergeConsecutive(sub))
}

predicate ValidOutput(s: string, evenCount: int, oddCount: int)
    requires ValidInput(s)
{
    evenCount >= 0 && oddCount >= 0 &&
    evenCount + oddCount >= |s| &&
    oddCount >= |s| &&
    (|s| == 1 ==> evenCount == 0 && oddCount == 1)
}

// <vc-helpers>
ghost function SingleCharsGood(s: string): int
    requires ValidInput(s)
{
    |s|
}
// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (evenCount: int, oddCount: int)
    requires ValidInput(s)
    ensures ValidOutput(s, evenCount, oddCount)
// </vc-spec>
// <vc-code>
{
  var even := 0;
  var odd := 0;
  ghost var min_odd := 0;
  for i := 0 to |s|-1
    invariant 0 <= i
    invariant even >= 0
    invariant odd >= 0
    invariant even + odd >= 0
    invariant min_odd == i
    invariant odd >= min_odd
  {
    var local_even := 0;
    var local_odd := 0;
    for j := i to |s|-1
      invariant i <= j <= |s|-1 || j == |s|
      invariant local_even >= 0
      invariant local_odd >= 0
      invariant local_even + local_odd >= 0
    {
      var sub := s[i..j+1];
      var len := j+1-i;
      if IsGoodSubstring(s, i, j) {
        if len %2 == 0 { local_even := local_even + 1; } else { local_odd := local_odd + 1; }
      }
    }
    even := even + local_even;
    odd := odd + local_odd;
    min_odd := min_odd + 1;  // since local_odd >= 1 always, as the single char is good
  }
  evenCount := even;
  oddCount := odd;
}
// </vc-code>

