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
lemma ValidInputPred(n: int, h1: seq<int>, h2: seq<int>)
  requires ValidInput(n, h1, h2) && n >= 2
  ensures ValidInput(n - 1, h1, h2)
{
  assert n - 1 >= 1;
  assert |h1| >= n - 1;
  assert |h2| >= n - 1;

  assert forall i :: 0 <= i < n - 1 ==> h1[i] >= 0;
  assert forall i :: 0 <= i < n - 1 ==> h2[i] >= 0;
}

lemma Row1NonNeg(n: int, h1: seq<int>, h2: seq<int>)
  requires ValidInput(n, h1, h2)
  ensures maxHeightEndingInRow1(n, h1, h2) >= 0
  decreases n
{
  if n == 1 {
    assert h1[0] >= 0;
  } else {
    assert n >= 2;
    ValidInputPred(n, h1, h2);
    Row2NonNeg(n - 1, h1, h2);
    Row1NonNeg(n - 1, h1, h2);
    assert 0 <= n - 1 && n - 1 < n;
    assert h1[n - 1] >= 0;
    assert maxHeightEndingInRow2(n - 1, h1, h2) >= 0;
    assert maxHeightEndingInRow1(n - 1, h1, h2) >= 0;
    assert maxHeightEndingInRow2(n - 1, h1, h2) + h1[n - 1] >= 0;
  }
}

lemma Row2NonNeg(n: int, h1: seq<int>, h2: seq<int>)
  requires ValidInput(n, h1, h2)
  ensures maxHeightEndingInRow2(n, h1, h2) >= 0
  decreases n
{
  if n == 1 {
    assert h2[0] >= 0;
  } else {
    assert n >= 2;
    ValidInputPred(n, h1, h2);
    Row1NonNeg(n - 1, h1, h2);
    Row2NonNeg(n - 1, h1, h2);
    assert 0 <= n - 1 && n - 1 < n;
    assert h2[n - 1] >= 0;
    assert maxHeightEndingInRow1(n - 1, h1, h2) >= 0;
    assert maxHeightEndingInRow2(n - 1, h1, h2) >= 0;
    assert maxHeightEndingInRow1(n - 1, h1, h2) + h2[n - 1] >= 0;
  }
}

lemma MaxTeamHeightNonNeg(n: int, h1: seq<int>, h2: seq<int>)
  requires ValidInput(n, h1, h2)
  ensures maxTeamHeight(n, h1, h2) >= 0
{
  Row1NonNeg(n, h1, h2);
  Row2NonNeg(n, h1, h2);
  assert maxHeightEndingInRow1(n, h1, h2) >= 0;
  assert maxHeightEndingInRow2(n, h1, h2) >= 0;
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
  MaxTeamHeightNonNeg(n, h1, h2);
  result := maxTeamHeight(n, h1, h2);
}
// </vc-code>

