// <vc-preamble>
predicate ValidInput(da: int, db: int)
{
  1 <= da <= 9 && 1 <= db <= 9
}

function FirstDigit(n: int): int
  requires n > 0
{
  if n < 10 then n else FirstDigit(n / 10)
}

predicate ValidSolution(da: int, db: int, result: seq<int>)
  requires ValidInput(da, db)
{
  if |result| == 2 then
    var a := result[0];
    var b := result[1];
    a > 0 && b > 0 && a <= 1000000000 && b <= 1000000000 &&
    b == a + 1 && FirstDigit(a) == da && FirstDigit(b) == db
  else if |result| == 1 then
    result[0] == -1
  else
    false
}

predicate IsPossible(da: int, db: int)
  requires ValidInput(da, db)
{
  (da == 9 && db == 1) || (da == db - 1) || (da == db)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(da: int, db: int) returns (result: seq<int>)
  requires ValidInput(da, db)
  ensures ValidSolution(da, db, result)
  ensures IsPossible(da, db) <==> |result| == 2
  ensures !IsPossible(da, db) <==> result == [-1]
// </vc-spec>
// <vc-code>
{
  if da == 9 && db == 1 {
    result := [9, 10];
  } else if da == db - 1 {
    result := [da, db];
  } else if da == db {
    result := [da * 10, da * 10 + 1];
  } else {
    result := [-1];
  }
}
// </vc-code>
