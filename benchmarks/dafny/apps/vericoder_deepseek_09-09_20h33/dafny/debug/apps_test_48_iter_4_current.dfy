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
lemma countLessValueMonotonic(n: int, m: int, target1: int, target2: int)
  requires n >= 0 && m >= 1
  requires target1 >= 1 && target2 >= 1
  requires target1 <= target2
  ensures countLessValue(n, m, target1) <= countLessValue(n, m, target2)
  decreases n
{
  if n == 0 {
  } else {
    var maxJ1 := (target1 - 1) / n;
    var maxJ2 := (target2 - 1) / n;
    var actualMaxJ1 := if maxJ1 > m then m else maxJ1;
    var actualMaxJ2 := if maxJ2 > m then m else maxJ2;
    assert actualMaxJ1 <= actualMaxJ2;
    countLessValueMonotonic(n - 1, m, target1, target2);
  }
}

lemma countLessOrEqualValueMonotonic(n: int, m: int, target1: int, target2: int)
  requires n >= 1 && m >= 1
  requires target1 >= 0 && target2 >= 0
  requires target1 <= target2
  ensures countLessOrEqualValue(n, m, target1) <= countLessOrEqualValue(n, m, target2)
{
  if target1 == target2 {
  } else if target2 <= 0 {
    assert countLessOrEqualValue(n, m, target1) == 0;
    assert countLessOrEqualValue(n, m, target2) == 0;
  } else if target1 <= 0 {
    assert countLessOrEqualValue(n, m, target1) == 0;
    assert countLessOrEqualValue(n, m, target2) >= 0;
  } else if target2 >= n * m {
    assert countLessOrEqualValue(n, m, target2) == n * m;
    assert countLessOrEqualValue(n, m, target1) <= n * m;
  } else {
    if target1 + 1 <= target2 + 1 {
      countLessValueMonotonic(n, m, target1 + 1, target2 + 1);
      assert countLessValue(n, m, target1 + 1) <= countLessValue(n, m, target2 + 1);
    }
  }
}

lemma countLessValueBounds(n: int, m: int, target: int)
  requires n >= 0 && m >= 1 && target >= 1
  ensures 0 <= countLessValue(n, m, target) <= n * m
{
}

lemma countLessOrEqualValueBounds(n: int, m: int, target: int)
  requires n >= 1 && m >= 1 && target >= 0
  ensures 0 <= countLessOrEqualValue(n, m, target) <= n * m
{
}

lemma countLessOrEqualValuePreserved(n: int, m: int, low: int, high: int, k: int, mid: int, count: int)
  requires ValidInput(n, m, k)
  requires 1 <= low <= high <= n * m
  requires countLessOrEqualValue(n, m, low - 1) < k
  requires countLessOrEqualValue(n, m, high) >= k
  requires mid == low + (high - low) / 2
  requires count == countLessOrEqualValue(n, m, mid)
  ensures (count >= k ==> countLessOrEqualValue(n, m, mid - 1) >= k || mid == 1) 
  ensures (count < k ==> countLessOrEqualValue(n, m, low - 1) < k && countLessOrEqualValue(n, m, mid + 1) > count)
{
  if count >= k {
    if mid > 1 {
      countLessOrEqualValueMonotonic(n, m, mid - 1, mid);
    }
  } else {
    countLessOrEqualValueMonotonic(n, m, mid, mid + 1);
    assert countLessOrEqualValue(n, m, mid + 1) > count;
  }
}

lemma binarySearchInvariantMaintenance(n: int, m: int, low: int, high: int, k: int, mid: int, count: int)
  requires ValidInput(n, m, k)
  requires 1 <= low <= high <= n * m
  requires countLessOrEqualValue(n, m, low - 1) < k
  requires countLessOrEqualValue(n, m, high) >= k
  requires mid == low + (high - low) / 2
  requires count == countLessOrEqualValue(n, m, mid)
{
  if count >= k {
    assert countLessOrEqualValue(n, m, high) >= k;
    assert countLessOrEqualValue(n, m, mid - 1) >= k || mid == 1;
  } else {
    assert countLessOrEqualValue(n, m, low - 1) < k;
    assert countLessOrEqualValue(n, m, mid + 1) > count;
  }
}
// </vc-helpers>
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
  assert countLessOrEqualValue(n, m, high) == n * m >= k;
  assert countLessOrEqualValue(n, m, low - 1) == countLessOrEqualValue(n, m, 0) == 0 < k;
  
  while low <= high
    invariant 1 <= low <= high + 1
    invariant high <= n * m
    invariant countLessOrEqualValue(n, m, low - 1) < k
    invariant countLessOrEqualValue(n, m, high) >= k
  {
    var mid := low + (high - low) / 2;
    var count := countLessOrEqualValue(n, m, mid);
    
    binarySearchInvariantMaintenance(n, m, low, high, k, mid, count);
    
    if count >= k {
      high := mid - 1;
      assert countLessOrEqualValue(n, m, high) >= countLessOrEqualValue(n, m, mid - 1) >= k || mid == 1;
    } else {
      low := mid + 1;
      assert countLessOrEqualValue(n, m, low - 1) == count < k;
      assert countLessOrEqualValue(n, m, high) >= k;
    }
  }
  
  result := low;
}
// </vc-code>

