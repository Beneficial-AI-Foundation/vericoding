// <vc-preamble>

predicate HasPairSumToZero(l: seq<int>)
{
    exists i, j :: 0 <= i < j < |l| && l[i] + l[j] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method pairs_sum_to_zero(l: seq<int>) returns (result: bool)
    ensures result == HasPairSumToZero(l)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [Added loop invariants to prove postcondition] */
  result := false;
  var i: nat := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant !result ==> forall k, j :: 0 <= k < i && k < j < |l| ==> l[k] + l[j] != 0
  {
    var j: nat := i + 1;
    while j < |l|
      invariant i < j <= |l|
      invariant !result ==> forall k :: i < k < j ==> l[i] + l[k] != 0
    {
      if l[i] + l[j] == 0 
      {
        result := true;
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
