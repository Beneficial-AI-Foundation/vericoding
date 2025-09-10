function countLessValue(n: int, m: int, target: int): int
  requires n >= 0 && m >= 1 && target >= 1
  ensures countLessValue(n, m, target) >= 0
  ensures countLessValue(n, m, target) <= n * m
{
  if n == 0 then 0
  else 
    var maxJ := (target - 1) / n;
    var actualMaxJ := if maxJ > m then m else maxJ;
    var contribution := if actualMaxJ >= 1 then actualMaxJ else 0;
    contribution + countLessValue(n - 1, m, target)
}

function countLessOrEqualValue(n: int, m: int, target: int): int
  requires n >= 1 && m >= 1 && target >= 0
  ensures countLessOrEqualValue(n, m, target) >= 0
  ensures countLessOrEqualValue(n, m, target) <= n * m
{
  if target <= 0 then 0
  else if target >= n * m then n * m
  else countLessValue(n, m, target + 1)
}

predicate ValidInput(n: int, m: int, k: int)
{
  1 <= n <= 500000 && 1 <= m <= 500000 && 1 <= k <= n * m
}

// <vc-helpers>
function countLess(
    n: int,
    m: int,
    target: int
  ): int
  requires n >= 0 && m >= 1 && target >= 1
  ensures countLess(n, m, target) >= 0
  ensures countLess(n, m, target) <= n * m
{
  if n == 0 then 0 else n * min(m, (target - 1) / n)
}

function countLessOrEqual(
    n: int,
    m: int,
    target: int
  ): int
  requires n >= 1 && m >= 1 && target >= 0
  ensures countLessOrEqual(n, m, target) >= 0
  ensures countLessOrEqual(n, m, target) <= n * m
{
  if target <= 0 then 0
  else if target >= n * m then n * m
  else countLess(n, m, target + 1)
}

function min(a: int, b: int): int {
  if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int) returns (result: int)
  requires ValidInput(n, m, k)
  ensures 1 <= result <= n * m
  ensures countLessOrEqualValue(n, m, result) >= k
  ensures result == 1 || countLessOrEqualValue(n, m, result - 1) < k
// </vc-spec>
// <vc-code>
{
  var low := 1;
  var high := n * m;
  var ans := n * m;

  while low <= high
    invariant 1 <= low <= (n * m) + 1
    invariant 0 <= high <= n * m
    invariant ans == high + 1 || ans == (n * m)
    invariant countLessOrEqual(n, m, ans) >= k
    invariant low <= ans
  {
    var mid := low + (high - low) / 2;
    var count := countLessOrEqual(n, m, mid);

    if count >= k
    {
      ans := mid;
      high := mid - 1;
    } else
    {
      low := mid + 1;
    }
  }
  result := ans;
}
// </vc-code>

