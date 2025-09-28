// <vc-preamble>
function popcount(n: nat): nat {
  if n == 0 then 0
  else popcount(n / 2) + n % 2
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed lemma preconditions and logic for correct bubble sort verification */
lemma SwapPreservesOrder(a: seq<nat>, i: int, j: int)
  requires 0 <= i < j < |a|
  requires forall x, y :: 0 <= x < y < i ==> popcount(a[x]) <= popcount(a[y])
  requires forall x, y :: j < x < y < |a| ==> popcount(a[x]) <= popcount(a[y])
  requires popcount(a[i]) > popcount(a[j])
  ensures var swapped := a[i := a[j]][j := a[i]];
          forall x, y :: 0 <= x < y < i ==> popcount(swapped[x]) <= popcount(swapped[y])
{
  var swapped := a[i := a[j]][j := a[i]];
  forall x, y | 0 <= x < y < i
    ensures popcount(swapped[x]) <= popcount(swapped[y])
  {
    assert swapped[x] == a[x];
    assert swapped[y] == a[y];
  }
}

lemma SwapPreservesRightOrder(a: seq<nat>, j: int)
  requires 0 < j < |a|
  requires forall x, y :: j+1 < x < y < |a| ==> popcount(a[x]) <= popcount(a[y])
  ensures var swapped := a[j-1 := a[j]][j := a[j-1]];
          forall x, y :: j+1 < x < y < |a| ==> popcount(swapped[x]) <= popcount(swapped[y])
{
  var swapped := a[j-1 := a[j]][j := a[j-1]];
  forall x, y | j+1 < x < y < |a|
    ensures popcount(swapped[x]) <= popcount(swapped[y])
  {
    assert swapped[x] == a[x];
    assert swapped[y] == a[y];
  }
}

lemma SwapMaintainsPartialOrder(a: seq<nat>, j: int, i: int)
  requires 0 < j <= i < |a|
  requires forall x, y :: 0 <= x < y < j ==> popcount(a[x]) <= popcount(a[y])
  requires forall x, y :: j <= x < y <= i ==> popcount(a[x]) <= popcount(a[y])
  requires popcount(a[j-1]) > popcount(a[j])
  ensures var swapped := a[j-1 := a[j]][j := a[j-1]];
          forall x, y :: j-1 <= x < y <= i ==> popcount(swapped[x]) <= popcount(swapped[y])
{
  var swapped := a[j-1 := a[j]][j := a[j-1]];
  forall x, y | j-1 <= x < y <= i
    ensures popcount(swapped[x]) <= popcount(swapped[y])
  {
    if x == j-1 && y == j {
      assert popcount(swapped[x]) == popcount(a[j]) < popcount(a[j-1]) == popcount(swapped[y]);
    } else if x == j-1 && y > j {
      assert popcount(swapped[x]) == popcount(a[j]) <= popcount(a[y]) == popcount(swapped[y]);
    } else if x < j-1 && y == j {
      assert popcount(swapped[x]) == popcount(a[x]) <= popcount(a[j-1]) == popcount(swapped[y]);
    } else {
      assert popcount(swapped[x]) == popcount(a[x]) <= popcount(a[y]) == popcount(swapped[y]);
    }
  }
}
// </vc-helpers>

// <vc-spec>
method sort_array(s: seq<nat>) returns (sorted: seq<nat>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> popcount(sorted[i]) <= popcount(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed lemma calls with correct preconditions */
  var result: seq<nat> := s;
  var i := 0;
  while i < |result|
    invariant 0 <= i <= |result|
    invariant |result| == |s|
    invariant multiset(result) == multiset(s)
    invariant forall x, y :: 0 <= x < y < i ==> popcount(result[x]) <= popcount(result[y])
  {
    var j := i;
    while j > 0 && popcount(result[j-1]) > popcount(result[j])
      invariant 0 <= j <= i
      invariant |result| == |s|
      invariant multiset(result) == multiset(s)
      invariant forall x, y :: 0 <= x < y < j ==> popcount(result[x]) <= popcount(result[y])
      invariant forall x, y :: j <= x < y <= i ==> popcount(result[x]) <= popcount(result[y])
      invariant j == i || popcount(result[j]) <= popcount(result[j+1])
    {
      var temp := result[j-1];
      SwapMaintainsPartialOrder(result, j, i);
      result := result[j-1 := result[j]][j := temp];
      j := j - 1;
    }
    i := i + 1;
  }
  sorted := result;
}
// </vc-code>
