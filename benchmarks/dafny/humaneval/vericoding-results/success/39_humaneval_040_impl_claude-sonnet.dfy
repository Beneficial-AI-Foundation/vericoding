// <vc-preamble>

predicate HasTripleSumToZero(l: seq<int>)
{
    exists i, j, k :: 0 <= i < j < k < |l| && l[i] + l[j] + l[k] == 0
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method triples_sum_to_zero(l: seq<int>) returns (result: bool)
    ensures result == HasTripleSumToZero(l)
// </vc-spec>
// <vc-code>
{
  if |l| < 3 {
    result := false;
    return;
  }
  
  var i := 0;
  while i < |l| - 2
    invariant 0 <= i <= |l| - 2
    invariant !exists ii, jj, kk :: 0 <= ii < jj < kk < |l| && ii < i && l[ii] + l[jj] + l[kk] == 0
  {
    var j := i + 1;
    while j < |l| - 1
      invariant i + 1 <= j <= |l| - 1
      invariant !exists ii, jj, kk :: 0 <= ii < jj < kk < |l| && ii < i && l[ii] + l[jj] + l[kk] == 0
      invariant !exists jj, kk :: i < jj < kk < |l| && jj < j && l[i] + l[jj] + l[kk] == 0
    {
      var k := j + 1;
      while k < |l|
        invariant j + 1 <= k <= |l|
        invariant !exists ii, jj, kk :: 0 <= ii < jj < kk < |l| && ii < i && l[ii] + l[jj] + l[kk] == 0
        invariant !exists jj, kk :: i < jj < kk < |l| && jj < j && l[i] + l[jj] + l[kk] == 0
        invariant !exists kk :: j < kk < |l| && kk < k && l[i] + l[j] + l[kk] == 0
      {
        if l[i] + l[j] + l[k] == 0 {
          result := true;
          return;
        }
        k := k + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  result := false;
}
// </vc-code>
