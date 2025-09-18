// <vc-preamble>
function CountOccurrences(nums: seq<int>, value: int): nat
{
    |set i | 0 <= i < |nums| && nums[i] == value|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): iterative Boyer-Moore using recursion with termination */
function BM(s: seq<int>): (int, int)
  decreases |s|
{
  if |s| == 0 then (0, 0)
  else
    var p := BM(s[1..]);
    if p.1 == 0 then (s[0], 1)
    else if p.0 == s[0] then (p.0, p.1 + 1) else (p.0, p.1 - 1)
}

/* helper modified by LLM (iteration 5): returns candidate from BM */
function Candidate(s: seq<int>): int
{
  BM(s).0
}
// </vc-helpers>

// <vc-spec>
method MajorityElement(nums: array<int>) returns (result: int)
    requires nums.Length > 0
    ensures var numsSeq := nums[..];
            var n := |numsSeq|;
            CountOccurrences(numsSeq, result) > n / 2 &&
            forall x: int :: x == result || CountOccurrences(numsSeq, x) <= n / 2
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): compute BM candidate and count using CountOccurrences for prefixes */
  var numsSeq := nums[..];
  var n := |numsSeq|;
  var cand := Candidate(numsSeq);
  var cnt: nat := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= cnt <= i
    invariant cnt == CountOccurrences(numsSeq[..i], cand)
    decreases n - i
  {
    if numsSeq[i] == cand {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  assert cnt == CountOccurrences(numsSeq, cand);
  assert cnt > n / 2;
  result := cand;
}
// </vc-code>
