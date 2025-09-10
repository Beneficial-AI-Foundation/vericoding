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
lemma countLessValueMonotonic(n: int, m: int, x: int, y: int)
  requires n >= 0 && m >= 1
  requires x <= y && x >= 1 && y >= 1
  ensures countLessValue(n, m, x) >= countLessValue(n, m, y)
  decreases n
{
  if n == 0 {
    assert countLessValue(n, m, x) == 0;
    assert countLessValue(n, m, y) == 0;
  } else {
    var maxJx := (x - 1) / n;
    var maxJy := (y - 1) / n;
    assert x <= y;
    assert x - 1 <= y - 1;
    assert (x - 1) / n <= (y - 1) / n;
    assert maxJx <= maxJy;
    
    var actualMaxJx := if maxJx > m then m else maxJx;
    var actualMaxJy := if maxJy > m then m else maxJy;
    assert actualMaxJx <= actualMaxJy;
    
    var contributionX := if actualMaxJx >= 1 then actualMaxJx else 0;
    var contributionY := if actualMaxJy >= 1 then actualMaxJy else 0;
    assert contributionX <= contributionY;
    
    countLessValueMonotonic(n - 1, m, x, y);
  }
}

lemma countLessOrEqualMonotonic(n: int, m: int, x: int, y: int)
  requires n >= 1 && m >= 1
  requires x <= y
  requires x >= 0 && y >= 0
  ensures countLessOrEqualValue(n, m, x) <= countLessOrEqualValue(n, m, y)
{
  if x <= 0 {
    assert countLessOrEqualValue(n, m, x) == 0;
  } else if y <= 0 {
    assert false;
  } else if x >= n * m {
    assert countLessOrEqualValue(n, m, x) == n * m;
    assert countLessOrEqualValue(n, m, y) == n * m;
  } else if y >= n * m {
    assert countLessOrEqualValue(n, m, y) == n * m;
  } else {
    assert countLessOrEqualValue(n, m, x) == countLessValue(n, m, x + 1);
    assert countLessOrEqualValue(n, m, y) == countLessValue(n, m, y + 1);
    countLessValueMonotonic(n, m, x + 1, y + 1);
  }
}

lemma countLessValuePositive(n: int, m: int, target: int)
  requires n >= 1 && m >= 1 && target >= 2
  ensures countLessValue(n, m, target) >= 1
  decreases n
{
  if n == 1 {
    var maxJ := (target - 1) / 1;
    assert maxJ >= 1;
    var actualMaxJ := if maxJ > m then m else maxJ;
    assert actualMaxJ >= 1;
    var contribution := if actualMaxJ >= 1 then actualMaxJ else 0;
    assert contribution >= 1;
    assert countLessValue(0, m, target) == 0;
    assert countLessValue(n, m, target) == contribution + 0;
  } else {
    var maxJ := (target - 1) / n;
    var actualMaxJ := if maxJ > m then m else maxJ;
    var contribution := if actualMaxJ >= 1 then actualMaxJ else 0;
    if contribution >= 1 {
      assert countLessValue(n, m, target) >= 1;
    } else {
      countLessValuePositive(n - 1, m, target);
      assert countLessValue(n - 1, m, target) >= 1;
      assert countLessValue(n, m, target) >= 1;
    }
  }
}

lemma countAtLeastOne(n: int, m: int)
  requires n >= 1 && m >= 1
  ensures countLessOrEqualValue(n, m, 1) >= 1
{
  assert countLessOrEqualValue(n, m, 1) == countLessValue(n, m, 2);
  countLessValuePositive(n, m, 2);
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
    invariant countLessOrEqualValue(n, m, high) >= k
    invariant low == 1 || countLessOrEqualValue(n, m, low - 1) < k
    decreases high - low
  {
    var mid := low + (high - low) / 2;
    var count := countLessOrEqualValue(n, m, mid);
    
    if count >= k {
      high := mid;
    } else {
      low := mid + 1;
    }
  }
  
  result := low;
  
  if result > 1 {
    countLessOrEqualMonotonic(n, m, result - 1, result);
  }
}
// </vc-code>

