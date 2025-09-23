// <vc-preamble>
predicate ValidInput(n: int) {
  1 <= n <= 1000
}

predicate ValidOutput(result: int) {
  0 <= result < 1000000007
}

function computeBra(x: int, y: int): int
  requires x >= 0 && y >= 0
  decreases x + y
{
  if x == 0 && y == 0 then 0
  else
    var A := if (x + y) % 2 == 1 then 1 else 0;
    if x == y && x > 0 then A + computeBra(x-1, y)
    else if x == 0 && y > 0 then A + computeBra(x, y-1)
    else if y == 0 && x > 0 then A + computeBra(x-1, y)
    else if x < y && x != 0 && y != 0 then A + computeBra(x-1, y) + computeBra(x, y-1)
    else 0
}
// </vc-preamble>

// <vc-helpers>
method bra(x: int, y: int, ANS: array2<int>, mod: int) returns (res: int)
  requires x >= 0 && y >= 0
  requires x < ANS.Length0 && y < ANS.Length1
  requires ANS.Length0 > 0 && ANS.Length1 > 0
  requires mod > 0
  requires forall i, j :: 0 <= i < ANS.Length0 && 0 <= j < ANS.Length1 && ANS[i, j] != 0 ==> ANS[i, j] == computeBra(i, j) && ANS[i, j] >= 0
  modifies ANS
  decreases x + y
  ensures res >= 0
  ensures res == computeBra(x, y)
  ensures ANS[x, y] == res
  ensures forall i, j :: 0 <= i < ANS.Length0 && 0 <= j < ANS.Length1 && old(ANS[i, j]) != 0 ==> ANS[i, j] == old(ANS[i, j])
  ensures forall i, j :: 0 <= i < ANS.Length0 && 0 <= j < ANS.Length1 && ANS[i, j] != 0 ==> ANS[i, j] == computeBra(i, j) && ANS[i, j] >= 0
{
  if ANS[x, y] != 0 {
    res := ANS[x, y];
    return;
  }

  if x == 0 && y == 0 {
    ANS[x, y] := 0;
    res := 0;
    return;
  }

  var A: int;
  if (x + y) % 2 == 1 {
    A := 1;
  } else {
    A := 0;
  }

  if x == y && x > 0 {
    var temp := bra(x-1, y, ANS, mod);
    ANS[x, y] := A + temp;
    res := ANS[x, y];
  } else if x == 0 && y > 0 {
    var temp := bra(x, y-1, ANS, mod);
    ANS[x, y] := A + temp;
    res := ANS[x, y];
  } else if y == 0 && x > 0 {
    var temp := bra(x-1, y, ANS, mod);
    ANS[x, y] := A + temp;
    res := ANS[x, y];
  } else if x < y && x != 0 && y != 0 {
    var temp1 := bra(x-1, y, ANS, mod);
    var temp2 := bra(x, y-1, ANS, mod);
    ANS[x, y] := A + temp1 + temp2;
    res := ANS[x, y];
  } else {
    ANS[x, y] := 0;
    res := 0;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
  requires ValidInput(n)
  ensures ValidOutput(result)
  ensures result == computeBra(n, n) % 1000000007
// </vc-spec>
// <vc-code>
{
  var mod := 1000000007;
  var ANS := new int[n+1, n+1];

  // Initialize array to 0
  var i := 0;
  while i <= n
    invariant 0 <= i <= n+1
    invariant forall i', j' :: 0 <= i' < i && 0 <= j' <= n ==> ANS[i', j'] == 0
  {
    var j := 0;
    while j <= n
      invariant 0 <= j <= n+1
      invariant forall i', j' :: 0 <= i' < i && 0 <= j' <= n ==> ANS[i', j'] == 0
      invariant forall j' :: 0 <= j' < j ==> ANS[i, j'] == 0
    {
      ANS[i, j] := 0;
      j := j + 1;
    }
    i := i + 1;
  }

  result := bra(n, n, ANS, mod);
  result := result % mod;
}
// </vc-code>
