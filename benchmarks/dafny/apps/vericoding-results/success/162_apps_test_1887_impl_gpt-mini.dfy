predicate ValidInput(n: int, h1: seq<int>, h2: seq<int>)
{
    n >= 1 && |h1| >= n && |h2| >= n &&
    (forall i :: 0 <= i < n ==> h1[i] >= 0) &&
    (forall i :: 0 <= i < n ==> h2[i] >= 0)
}

function maxTeamHeight(n: int, h1: seq<int>, h2: seq<int>): int
    requires ValidInput(n, h1, h2)
{
    var dp1 := maxHeightEndingInRow1(n, h1, h2);
    var dp2 := maxHeightEndingInRow2(n, h1, h2);
    if dp1 > dp2 then dp1 else dp2
}

function maxHeightEndingInRow1(n: int, h1: seq<int>, h2: seq<int>): int
    requires ValidInput(n, h1, h2)
    decreases n
{
    if n == 1 then h1[0]
    else
        var prevRow2 := maxHeightEndingInRow2(n-1, h1, h2);
        var prevRow1 := maxHeightEndingInRow1(n-1, h1, h2);
        var takeFromRow2 := prevRow2 + h1[n-1];
        if takeFromRow2 > prevRow1 then takeFromRow2 else prevRow1
}

function maxHeightEndingInRow2(n: int, h1: seq<int>, h2: seq<int>): int
    requires ValidInput(n, h1, h2)
    decreases n
{
    if n == 1 then h2[0]
    else
        var prevRow1 := maxHeightEndingInRow1(n-1, h1, h2);
        var prevRow2 := maxHeightEndingInRow2(n-1, h1, h2);
        var takeFromRow1 := prevRow1 + h2[n-1];
        if takeFromRow1 > prevRow2 then takeFromRow1 else prevRow2
}

// <vc-helpers>
lemma NonnegMaxHeights(n: int, h1: seq<int>, h2: seq<int>)
  requires ValidInput(n, h1, h2)
  ensures maxHeightEndingInRow1(n, h1, h2) >= 0
  ensures maxHeightEndingInRow2(n, h1, h2) >= 0
  decreases n
{
  if n == 1 {
    assert maxHeightEndingInRow1(n, h1, h2) == h1[0];
    assert h1[0] >= 0;
    assert maxHeightEndingInRow2(n, h1, h2) == h2[0];
    assert h2[0] >= 0;
  } else {
    NonnegMaxHeights(n-1, h1, h2);
    var prev1 := maxHeightEndingInRow1(n-1, h1, h2);
    var prev2 := maxHeightEndingInRow2(n-1, h1, h2);
    assert prev1 >= 0;
    assert prev2 >= 0;
    assert h1[n-1] >= 0;
    assert h2[n-1] >= 0;
    assert maxHeightEndingInRow1(n, h1, h2) ==
           (if prev2 + h1[n-1] > prev1 then prev2 + h1[n-1] else prev1);
    assert maxHeightEndingInRow2(n, h1, h2) ==
           (if prev1 + h2[n-1] > prev2 then prev1 + h2[n-1] else prev2);
    if prev2 + h1[n-1] > prev1 {
      assert maxHeightEndingInRow1(n, h1, h2) >= 0;
    } else {
      assert maxHeightEndingInRow1(n, h1, h2) >= 0;
    }
    if prev1 + h2[n-1] > prev2 {
      assert maxHeightEndingInRow2(n, h1, h2) >= 0;
    } else {
      assert maxHeightEndingInRow2(n, h1, h2) >= 0;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, h1: seq<int>, h2: seq<int>) returns (result: int)
    requires ValidInput(n, h1, h2)
    ensures result >= 0
    ensures result == maxTeamHeight(n, h1, h2)
// </vc-spec>
// <vc-code>
{
  var i := 1;
  var dp1 := h1[0];
  var dp2 := h2[0];
  while i < n
    invariant 1 <= i <= n
    invariant dp1 == maxHeightEndingInRow1(i, h1, h2)
    invariant dp2 == maxHeightEndingInRow2(i, h1, h2)
  {
    var newDp1 := if dp2 + h1[i] > dp1 then dp2 + h1[i] else dp1;
    var newDp2 := if dp1 + h2[i] > dp2 then dp1 + h2[i] else dp2;
    dp1 := newDp1;
    dp2 := newDp2;
    i := i + 1;
  }
  // Prove nonnegativity of the computed heights
  NonnegMaxHeights(n, h1, h2);
  assert dp1 >= 0;
  assert dp2 >= 0;
  if dp1 > dp2 { result := dp1; } else { result := dp2; }
}
// </vc-code>

