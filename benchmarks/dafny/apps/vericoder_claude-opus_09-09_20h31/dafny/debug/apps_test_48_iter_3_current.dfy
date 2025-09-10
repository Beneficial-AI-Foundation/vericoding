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
lemma CountLessOrEqualMonotonic(n: int, m: int, x: int, y: int)
  requires n >= 1 && m >= 1
  requires 0 <= x <= y
  ensures countLessOrEqualValue(n, m, x) <= countLessOrEqualValue(n, m, y)
{
  if x <= 0 {
    assert countLessOrEqualValue(n, m, x) == 0;
    if y >= n * m {
      assert countLessOrEqualValue(n, m, y) == n * m;
    }
  } else if y >= n * m {
    assert countLessOrEqualValue(n, m, y) == n * m;
    assert countLessOrEqualValue(n, m, x) <= n * m;
  } else {
    assert countLessOrEqualValue(n, m, x) == countLessValue(n, m, x + 1);
    assert countLessOrEqualValue(n, m, y) == countLessValue(n, m, y + 1);
    CountLessValueMonotonic(n, m, x + 1, y + 1);
  }
}

lemma CountLessValueMonotonic(n: int, m: int, x: int, y: int)
  requires n >= 0 && m >= 1
  requires 1 <= x <= y
  ensures countLessValue(n, m, x) <= countLessValue(n, m, y)
  decreases n
{
  if n == 0 {
    // Base case: both are 0
    assert countLessValue(n, m, x) == 0;
    assert countLessValue(n, m, y) == 0;
  } else {
    var maxJx := (x - 1) / n;
    var actualMaxJx := if maxJx > m then m else maxJx;
    var contributionX := if actualMaxJx >= 1 then actualMaxJx else 0;
    
    var maxJy := (y - 1) / n;
    var actualMaxJy := if maxJy > m then m else maxJy;
    var contributionY := if actualMaxJy >= 1 then actualMaxJy else 0;
    
    // Since x <= y and n > 0, we have (x-1)/n <= (y-1)/n
    assert x - 1 <= y - 1;
    assert (x - 1) / n <= (y - 1) / n;
    assert maxJx <= maxJy;
    
    // This implies actualMaxJx <= actualMaxJy
    if maxJx > m {
      assert actualMaxJx == m;
      if maxJy > m {
        assert actualMaxJy == m;
      } else {
        assert actualMaxJy == maxJy >= maxJx > m;
        assert actualMaxJy >= m;
      }
      assert actualMaxJx <= actualMaxJy;
    } else {
      assert actualMaxJx == maxJx;
      if maxJy > m {
        assert actualMaxJy == m >= maxJx == actualMaxJx;
      } else {
        assert actualMaxJy == maxJy >= maxJx == actualMaxJx;
      }
      assert actualMaxJx <= actualMaxJy;
    }
    
    // And therefore contributionX <= contributionY
    assert contributionX <= contributionY;
    
    // Recursive call
    CountLessValueMonotonic(n - 1, m, x, y);
    
    // Combine results
    assert countLessValue(n, m, x) == contributionX + countLessValue(n - 1, m, x);
    assert countLessValue(n, m, y) == contributionY + countLessValue(n - 1, m, y);
    assert countLessValue(n - 1, m, x) <= countLessValue(n - 1, m, y);
    assert contributionX + countLessValue(n - 1, m, x) <= contributionY + countLessValue(n - 1, m, y);
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

