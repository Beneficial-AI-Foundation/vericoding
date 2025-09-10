function CountCellsDivisibleByM(n: int, m: int): int
  requires 1 <= n
  requires 1 <= m
{
  |set i, j | 1 <= i <= n && 1 <= j <= n && (i * i + j * j) % m == 0 :: (i, j)|
}

predicate ValidInput(n: int, m: int) {
  1 <= n && 1 <= m <= 1000
}

// <vc-helpers>
lemma CountCellsNonNegative(n: int, m: int)
  requires 1 <= n && 1 <= m
  ensures CountCellsDivisibleByM(n, m) >= 0
{
  var s := set i, j | 1 <= i <= n && 1 <= j <= n && (i * i + j * j) % m == 0 :: (i, j);
  assert |s| >= 0;
}

lemma CountCellsByIteration(n: int, m: int)
  requires 1 <= n && 1 <= m
  ensures CountCellsDivisibleByM(n, m) == CountByLoop(n, m)
{
  var s := set i, j | 1 <= i <= n && 1 <= j <= n && (i * i + j * j) % m == 0 :: (i, j);
  CountByLoopCorrect(n, m);
}

function CountByLoop(n: int, m: int): int
  requires 1 <= n && 1 <= m
{
  CountByLoopHelper(n, n, m)
}

function CountByLoopHelper(i: int, n: int, m: int): int
  requires 0 <= i <= n
  requires 1 <= n && 1 <= m
{
  if i == 0 then 0
  else CountByLoopHelper(i - 1, n, m) + CountRowCells(i, n, m)
}

function CountRowCells(i: int, n: int, m: int): int
  requires 1 <= i <= n
  requires 1 <= n && 1 <= m
{
  CountRowCellsHelper(i, n, n, m)
}

function CountRowCellsHelper(i: int, j: int, n: int, m: int): int
  requires 1 <= i <= n
  requires 0 <= j <= n
  requires 1 <= n && 1 <= m
{
  if j == 0 then 0
  else CountRowCellsHelper(i, j - 1, n, m) + (if (i * i + j * j) % m == 0 then 1 else 0)
}

lemma CountByLoopCorrect(n: int, m: int)
  requires 1 <= n && 1 <= m
  ensures CountByLoop(n, m) == |set i, j | 1 <= i <= n && 1 <= j <= n && (i * i + j * j) % m == 0 :: (i, j)|
{
  CountByLoopHelperCorrect(n, n, m);
}

lemma CountByLoopHelperCorrect(i: int, n: int, m: int)
  requires 0 <= i <= n
  requires 1 <= n && 1 <= m
  ensures CountByLoopHelper(i, n, m) == |set x, y | 1 <= x <= i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)|
{
  if i == 0 {
    var s := set x, y | 1 <= x <= i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y);
    assert s == {};
  } else {
    CountByLoopHelperCorrect(i - 1, n, m);
    CountRowCellsCorrect(i, n, m);
    var s1 := set x, y | 1 <= x <= i - 1 && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y);
    var s2 := set y | 1 <= y <= n && (i * i + y * y) % m == 0 :: (i, y);
    var s := set x, y | 1 <= x <= i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y);
    assert s == s1 + s2;
    assert s1 * s2 == {};
  }
}

lemma CountRowCellsCorrect(i: int, n: int, m: int)
  requires 1 <= i <= n
  requires 1 <= n && 1 <= m
  ensures CountRowCells(i, n, m) == |set y | 1 <= y <= n && (i * i + y * y) % m == 0 :: (i, y)|
{
  CountRowCellsHelperCorrect(i, n, n, m);
}

lemma CountRowCellsHelperCorrect(i: int, j: int, n: int, m: int)
  requires 1 <= i <= n
  requires 0 <= j <= n
  requires 1 <= n && 1 <= m
  ensures CountRowCellsHelper(i, j, n, m) == |set y | 1 <= y <= j && (i * i + y * y) % m == 0 :: (i, y)|
{
  if j == 0 {
    var s := set y | 1 <= y <= j && (i * i + y * y) % m == 0 :: (i, y);
    assert s == {};
  } else {
    CountRowCellsHelperCorrect(i, j - 1, n, m);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: int)
  requires ValidInput(n, m)
  ensures result >= 0
  ensures result == CountCellsDivisibleByM(n, m)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant result == |set x, y | 1 <= x < i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)|
  {
    var j := 1;
    while j <= n
      invariant 1 <= j <= n + 1
      invariant result == |set x, y | 1 <= x < i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)| + 
                         |set y | 1 <= y < j && (i * i + y * y) % m == 0 :: (i, y)|
    {
      if (i * i + j * j) % m == 0 {
        result := result + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  CountCellsNonNegative(n, m);
}
// </vc-code>

