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
lemma DivisionMonotonic(a: int, b: int, c: int)
  requires b > 0
  requires a <= c
  ensures a / b <= c / b
{
  // For non-negative values, this holds
  if a >= 0 && c >= 0 {
    // Dafny can verify this case
  } else if a < 0 && c >= 0 {
    // a / b will be negative or zero, c / b will be non-negative
    assert a / b <= 0 <= c / b;
  } else if a < 0 && c < 0 {
    // Both negative - need more careful reasoning
    // When both are negative, division truncates toward negative infinity
    var qa := a / b;
    var qc := c / b;
    var ra := a - qa * b;
    var rc := c - qc * b;
    assert a == qa * b + ra && 0 <= ra < b;
    assert c == qc * b + rc && 0 <= rc < b;
    assert a <= c;
    assert qa * b + ra <= qc * b + rc;
    if qa > qc {
      assert (qa - qc) * b <= rc - ra;
      assert (qa - qc) * b < b;
      assert qa - qc < 1;
      assert qa - qc <= 0;
      assert false;
    }
    assert qa <= qc;
  }
}

lemma ContributionMonotonic(n: int, m: int, x: int, y: int)
  requires n > 0 && m >= 1
  requires 1 <= x <= y
  ensures 
    var maxJx := (x - 1) / n;
    var actualMaxJx := if maxJx > m then m else maxJx;
    var contributionX := if actualMaxJx >= 1 then actualMaxJx else 0;
    var maxJy := (y - 1) / n;
    var actualMaxJy := if maxJy > m then m else maxJy;
    var contributionY := if actualMaxJy >= 1 then actualMaxJy else 0;
    contributionX <= contributionY
{
  var maxJx := (x - 1) / n;
  var actualMaxJx := if maxJx > m then m else maxJx;
  var contributionX := if actualMaxJx >= 1 then actualMaxJx else 0;
  
  var maxJy := (y - 1) / n;
  var actualMaxJy := if maxJy > m then m else maxJy;
  var contributionY := if actualMaxJy >= 1 then actualMaxJy else 0;
  
  assert x - 1 >= 0 && y - 1 >= 0;
  DivisionMonotonic(x - 1, n, y - 1);
  assert maxJx <= maxJy;
  
  if maxJx > m && maxJy > m {
    assert actualMaxJx == m == actualMaxJy;
  } else if maxJx > m && maxJy <= m {
    assert false; // This case is impossible since maxJx <= maxJy
  } else if maxJx <= m && maxJy > m {
    assert actualMaxJx == maxJx <= m == actualMaxJy;
  } else {
    assert actualMaxJx == maxJx <= maxJy == actualMaxJy;
  }
}

lemma CountLessValueMonotonic(n: int, m: int, x: int, y: int)
  requires n >= 0 && m >= 1
  requires 1 <= x <= y
  ensures countLessValue(n, m, x) <= countLessValue(n, m, y)
  decreases n
{
  if n == 0 {
    // Base case
  } else {
    ContributionMonotonic(n, m, x, y);
    CountLessValueMonotonic(n - 1, m, x, y);
  }
}

lemma CountLessOrEqualMonotonic(n: int, m: int, x: int, y: int)
  requires n >= 1 && m >= 1
  requires 0 <= x <= y
  ensures countLessOrEqualValue(n, m, x) <= countLessOrEqualValue(n, m, y)
{
  if x <= 0 {
    assert countLessOrEqualValue(n, m, x) == 0;
  } else if y >= n * m {
    assert countLessOrEqualValue(n, m, y) == n * m;
  } else if x >= n * m {
    assert countLessOrEqualValue(n, m, x) == n * m;
    assert countLessOrEqualValue(n, m, y) == n * m;
  } else {
    CountLessValueMonotonic(n, m, x + 1, y + 1);
  }
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
  var lo := 1;
  var hi := n * m;
  
  while lo < hi
    invariant 1 <= lo <= hi <= n * m
    invariant countLessOrEqualValue(n, m, hi) >= k
    invariant lo == 1 || countLessOrEqualValue(n, m, lo - 1) < k
  {
    var mid := lo + (hi - lo) / 2;
    assert lo <= mid < hi;
    
    var count := countLessOrEqualValue(n, m, mid);
    
    if count < k {
      CountLessOrEqualMonotonic(n, m, lo - 1, mid);
      lo := mid + 1;
    } else {
      hi := mid;
    }
  }
  
  result := lo;
}
// </vc-code>

