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
/* helper modified by LLM (iteration 5): lemma connecting no-duplicate sequence to cardinality of its element set */
lemma Seq_noDup_cardinality(res: seq<int>)
  ensures |set k | 0 <= k < |res| :: res[k]| <= |res|
  ensures (forall i, j :: 0 <= i < j < |res| ==> res[i] != res[j]) ==> |set k | 0 <= k < |res| :: res[k]| == |res|
{
  if |res| == 0 {
    // empty sequence: both sides are 0
  } else {
    var tail := res[1..];
    Seq_noDup_cardinality(tail);
  }
}

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
  /* code modified by LLM (iteration 5): collect distinct positive elements preserving first occurrence order without using ghost values in runtime conditions */
  var res: seq<int> := [];
  ghost var seen: set<int> := {};
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant forall k :: 0 <= k < |res| ==> res[k] in l && IsPositive(res[k])
    invariant forall p, q :: 0 <= p < q < |res| ==> res[p] != res[q]
    invariant seen == (set k | 0 <= k < |res| :: res[k])
    invariant |res| == |seen|
    decreases |l| - i
  {
    if IsPositive(l[i]) {
      // check whether l[i] already appears in res using a runtime loop (no ghost in condition)
      var found := false;
      var j := 0;
      while j < |res|
        invariant 0 <= j <= |res|
        invariant found ==> (exists jj :: 0 <= jj < j && res[jj] == l[i])
        decreases |res| - j
      {
        if res[j] == l[i] {
          found := true;
        }
        j := j + 1;
      }
      if !found {
        res := res + [l[i]];
        ghost seen := seen + {l[i]};
      }
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>
