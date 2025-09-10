predicate ValidInput(a: seq<int>) {
  forall i :: 0 <= i < |a| ==> a[i] > 0
}

function CountFactorsOfTwo(n: int): int
  requires n > 0
  decreases n
{
  if n % 2 == 0 then 1 + CountFactorsOfTwo(n / 2)
  else 0
}

function SumFactors(a: seq<int>, i: int): int
  requires 0 <= i <= |a|
  requires forall j :: 0 <= j < |a| ==> a[j] > 0
  decreases |a| - i
{
  if i == |a| then 0
  else CountFactorsOfTwo(a[i]) + SumFactors(a, i + 1)
}

function MaxOperations(a: seq<int>): int
  requires ValidInput(a)
{
  SumFactors(a, 0)
}

// <vc-helpers>
function sumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else s[0] + sumSeq(s[1..])
}
// Predicate to prove that sum of CountFactorsOfTwo(a[j]) for j from i to |a|-1 is equal to SumFactors(a,i)
// No changes needed here, just adding a comment to clarify its purpose
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
  requires ValidInput(a)
  ensures result >= 0
  ensures result == MaxOperations(a)
// </vc-spec>
// <vc-code>
{
    var operations := 0;
    // Removed `b` array, as it was not used and could cause issues
    // if |a| == 0 then the loop range `0 to |a|-1` is invalid.
    // However, `ValidInput(a)` does not restrict empty sequences.
    // The `SumFactors` function also handles empty sequences.
    // If |a| == 0, the loop does not run, and operations remains 0.
    // MaxOperations also returns 0 in this case, so this is correct.
    for i := 0 to |a| - 1
        invariant 0 <= i <= |a|
        invariant operations == SumFactors(a, 0) - SumFactors(a, i)
        // Add additional invariant to prove CountFactorsOfTwo(a[j]) corresponds to collected operations
        invariant forall k :: 0 <= k < i ==> CountFactorsOfTwo(a[k]) == (SumFactors(a,k) - SumFactors(a,k+1))
    {
        var current_num := a[i];
        var count := 0;
        // While loop invariant proving `current_num` remains positive
        while current_num % 2 == 0
            invariant current_num > 0
            invariant current_num % 2 == 0 ==> current_num % 2 == 0 // This invariant is redundant.
            decreases current_num
        {
            count := count + 1;
            current_num := current_num / 2;
        }
        operations := operations + count;
        // The `b` array was removed, no need to update it
    }
    result := operations;
}
// </vc-code>

