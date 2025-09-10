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
lemma countLessOrEqualMonotonic(n: int, m: int, x: int, y: int)
  requires n >= 1 && m >= 1
  requires x <= y
  ensures countLessOrEqualValue(n, m, x) <= countLessOrEqualValue(n, m, y)
{
  if x <= 0 {
    assert countLessOrEqualValue(n, m, x) == 0;
  } else if y <= 0 {
    assert countLessOrEqualValue(n, m, y) == 0;
    assert countLessOrEqualValue(n, m, x) == 0;
  } else if x >= n * m {
    assert countLessOrEqualValue(n, m, x) == n * m;
    assert countLessOrEqualValue(n, m, y) == n * m;
  } else if y >= n * m {
    assert countLessOrEqualValue(n, m, y) == n * m;
  } else {
    assert countLessOrEqualValue(n, m, x) == countLessValue(n, m, x + 1);
    assert countLessOrEqualValue(n, m, y) == countLessValue(n, m, y + 1);
  }
}

lemma countAtLeastOne(n: int, m: int)
  requires n >= 1 && m >= 1
  ensures countLessOrEqualValue(n, m, 1) >= 1
{
  assert countLessOrEqualValue(n, m, 1) == countLessValue(n, m, 2);
}

lemma countAtMostNM(n: int, m: int, target: int)
  requires n >= 1 && m >= 1 && target >= n * m
  ensures countLessOrEqualValue(n, m, target) == n * m
{
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
  
  while low < high
    invariant 1 <= low <= high <= n * m
    invariant countLessOrEqualValue(n, m, low) >= k || low == 1
    invariant countLessOrEqualValue(n, m, high) >= k
    invariant low == 1 || countLessOrEqualValue(n, m, low - 1) < k
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    var count := countLessOrEqualValue(n, m, mid);
    
    if count >= k {
      high := mid;
      countLessOrEqualMonotonic(n, m, mid, high);
    } else {
      low := mid + 1;
      countLessOrEqualMonotonic(n, m, low - 1, mid);
    }
  }
  
  result := low;
  countAtLeastOne(n, m);
  countAtMostNM(n, m, result);
}
// </vc-code>

