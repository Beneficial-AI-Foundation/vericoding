// <vc-preamble>

predicate IsPositive(x: int)
{
    x > 0
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> IsPositive(s[i])
}

predicate AllElementsFromOriginal(result: seq<int>, original: seq<int>)
{
    forall x :: x in result ==> x in original
}

predicate ContainsAllPositives(result: seq<int>, original: seq<int>)
{
    forall i :: 0 <= i < |original| && IsPositive(original[i]) ==> original[i] in result
}

predicate PreservesOrder(result: seq<int>, original: seq<int>)
{
    forall i, j :: 0 <= i < j < |result| ==> 
        (exists k1, k2 :: (0 <= k1 < k2 < |original| && original[k1] == result[i] && original[k2] == result[j] &&
        forall k :: k1 < k < k2 ==> !IsPositive(original[k])))
}

function CountPositives(s: seq<int>): int
{
    |set x | x in s && IsPositive(x)|
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method get_positive(l: seq<int>) returns (result: seq<int>)
    ensures AllPositive(result)
    ensures AllElementsFromOriginal(result, l)
    ensures ContainsAllPositives(result, l)
    ensures |result| == CountPositives(l)
    ensures PreservesOrder(result, l)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): [Collect only unique positive numbers to satisfy the CountPositives postcondition.] */
  result := [];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant AllPositive(result)
    invariant AllElementsFromOriginal(result, l)
    invariant ContainsAllPositives(result, l[..i])
    invariant |result| == CountPositives(l[..i])
    invariant PreservesOrder(result, l)
    decreases |l| - i
  {
    if IsPositive(l[i]) && l[i] !in result {
      result := result + [l[i]];
    }
    i := i + 1;
  }
}
// </vc-code>
