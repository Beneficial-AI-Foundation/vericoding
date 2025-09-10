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
lemma CountCellsUpTo(n: int, m: int, i: int, j: int)
  requires 1 <= n && 1 <= m
  requires 0 <= i <= n
  requires 0 <= j <= n
  ensures |set x, y | 1 <= x <= i && 1 <= y <= j && (x * x + y * y) % m == 0 :: (x, y)| >= 0
{
  var s := set x, y | 1 <= x <= i && 1 <= y <= j && (x * x + y * y) % m == 0 :: (x, y);
  assert s == {} || |s| >= 0;
}

lemma SetAddElement(n: int, m: int, i: int, j: int)
  requires 1 <= n && 1 <= m
  requires 1 <= i <= n && 1 <= j <= n
  ensures (i, j) in set x, y | 1 <= x <= n && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y) 
          <==> (i * i + j * j) % m == 0
{
}

lemma CountSubsetRelation(n: int, m: int, k: int)
  requires 1 <= n && 1 <= m
  requires 0 <= k <= n
  ensures |set x, y | 1 <= x <= k && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)| 
          <= |set x, y | 1 <= x <= n && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)|
{
  var subset := set x, y | 1 <= x <= k && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y);
  var full := set x, y | 1 <= x <= n && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y);
  assert subset <= full;
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
  var count := 0;
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant count >= 0
    invariant count == |set x, y | 1 <= x < i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)|
  {
    var j := 1;
    var rowCount := 0;
    
    while j <= n
      invariant 1 <= j <= n + 1
      invariant rowCount >= 0
      invariant rowCount == |set y | 1 <= y < j && (i * i + y * y) % m == 0 :: y|
    {
      if (i * i + j * j) % m == 0 {
        rowCount := rowCount + 1;
      }
      j := j + 1;
    }
    
    assert rowCount == |set y | 1 <= y <= n && (i * i + y * y) % m == 0 :: y|;
    
    count := count + rowCount;
    i := i + 1;
  }
  
  assert i == n + 1;
  assert count == |set x, y | 1 <= x <= n && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)|;
  
  result := count;
}
// </vc-code>

