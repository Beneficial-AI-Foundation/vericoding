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
    for i := 0 to |a| - 1
        invariant 0 <= i <= |a|
        invariant operations == SumFactors(a, 0) - SumFactors(a, i)
        // Corrected invariant for partial sum: operations maintains sum of factors for elements processed so far.
        // It's equivalent to SumFactors(a[0..i]) if such a function existed, or more precisely,
        // it reflects the operations already accumulated based on the definition of SumFactors(a, 0) and SumFactors(a, i).
        invariant forall k :: 0 <= k < i ==> CountFactorsOfTwo(a[k]) == (SumFactors(a,k) - SumFactors(a,k+1))
    {
        var current_num := a[i];
        var count := 0;
        while current_num % 2 == 0
            invariant current_num > 0
            invariant old(current_num) == (current_num * (2 * count))  // Keep track of the original value relation for proof
            decreases current_num
        {
            count := count + 1;
            current_num := current_num / 2;
        }
        operations := operations + count;
    }
    result := operations;
}
// </vc-code>

