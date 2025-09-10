predicate ValidInput(n: int, scores: seq<int>)
{
    n == |scores| && n >= 1 && exists i :: 0 <= i < |scores| && scores[i] != 0
}

function UniqueNonZeroScores(scores: seq<int>): set<int>
{
    set i | 0 <= i < |scores| && scores[i] != 0 :: scores[i]
}

predicate ValidResult(scores: seq<int>, result: int)
{
    result >= 1 && 
    result == |UniqueNonZeroScores(scores)| && 
    result <= |scores|
}

// <vc-helpers>
function PrefixNonZero(scores: seq<int>, i: int): set<int>
  requires 0 <= i <= |scores|
{
  set k | 0 <= k < i && scores[k] != 0 :: scores[k]
}

lemma PrefixCardinalityBound(scores: seq<int>, i: int)
  requires 0 <= i <= |scores|
  ensures |PrefixNonZero(scores, i)| <= i
{
  if i == 0 {
    // empty prefix has size 0
  } else {
    PrefixCardinalityBound(scores, i - 1);
    if scores[i - 1] != 0 {
      // PrefixNonZero(scores, i) == PrefixNonZero(scores, i-1) + {scores[i-1]}
      // So its cardinality is at most |PrefixNonZero(scores,i-1)| + 1 <= (i-1)+1 = i
      assert PrefixNonZero(scores, i) ==
             (PrefixNonZero(scores, i - 1) + { scores[i - 1] });
      assert |PrefixNonZero(scores, i)| <= |PrefixNonZero(scores, i - 1)| + 1;
      assert |PrefixNonZero(scores, i)| <= (i - 1) + 1;
    } else {
      // no new element added
      assert PrefixNonZero(scores, i) == PrefixNonZero(scores, i - 1);
      assert |PrefixNonZero(scores, i)| <= i - 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, scores: seq<int>) returns (result: int)
    requires ValidInput(n, scores)
    ensures ValidResult(scores, result)
// </vc-spec>
// <vc-code>
{
  var s : set<int> := {};
  var i := 0;
  while i < |scores|
    invariant 0 <= i <= |scores|
    invariant forall k :: 0 <= k < i && scores[k] != 0 ==> scores[k] in s
    invariant forall v :: v in s ==> exists k :: 0 <= k < i && scores[k] != 0 && scores[k] == v
  {
    if scores[i] != 0 {
      if scores[i] in s {
        // already present, nothing to do
      } else {
        s := s + { scores[i] };
      }
    }
    i := i + 1;
  }

  // After processing all indices, s contains exactly the non-zero unique scores
  assert forall k :: 0 <= k < |scores| && scores[k] != 0 ==> scores[k] in s;
  assert forall v :: v in s ==> exists k :: 0 <= k < |scores| && scores[k] != 0 && scores[k] == v;
  assert s == UniqueNonZeroScores(scores);

  result := |s|;

  // result >= 1 follows from ValidInput (there exists at least one non-zero score)
  // and that value is in s
  // result <= n (|scores|) follows from PrefixCardinalityBound
  PrefixCardinalityBound(scores, |scores|);
  assert result <= |scores|;
  assert result >= 1;
}
// </vc-code>

