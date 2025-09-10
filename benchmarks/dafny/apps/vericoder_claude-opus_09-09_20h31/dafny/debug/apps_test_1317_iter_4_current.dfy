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
  ensures ((i, j) in set x, y | 1 <= x <= n && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)) 
          <==> ((i * i + j * j) % m == 0)
{
}

lemma RowCountLemma(n: int, m: int, i: int, j: int, rowCount: int)
  requires 1 <= n && 1 <= m
  requires 1 <= i <= n
  requires 1 <= j <= n + 1
  requires rowCount == |set y | 1 <= y < j && (i * i + y * y) % m == 0 :: y|
  ensures j <= n && (i * i + j * j) % m == 0 ==> 
    rowCount + 1 == |set y | 1 <= y <= j && (i * i + y * y) % m == 0 :: y|
  ensures j <= n && !((i * i + j * j) % m == 0) ==> 
    rowCount == |set y | 1 <= y <= j && (i * i + y * y) % m == 0 :: y|
{
  if j <= n {
    var setBefore := set y | 1 <= y < j && (i * i + y * y) % m == 0 :: y;
    var setAfter := set y | 1 <= y <= j && (i * i + y * y) % m == 0 :: y;
    
    if (i * i + j * j) % m == 0 {
      assert j !in setBefore;
      assert setAfter == setBefore + {j};
      assert |setAfter| == |setBefore| + 1;
    } else {
      assert j !in setAfter;
      assert setAfter == setBefore;
    }
  }
}

lemma SetDecomposition(n: int, m: int, i: int)
  requires 1 <= n && 1 <= m
  requires 1 <= i <= n + 1
  ensures i <= n ==> 
    |set x, y | 1 <= x < i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)| +
    |set y | 1 <= y <= n && (i * i + y * y) % m == 0 :: y| ==
    |set x, y | 1 <= x <= i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)|
{
  if i <= n {
    var setBeforeI := set x, y | 1 <= x < i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y);
    var rowI := set y | 1 <= y <= n && (i * i + y * y) % m == 0 :: y;
    var setWithI := set x, y | 1 <= x <= i && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y);
    
    var rowIPairs := set p | p in setWithI && p.0 == i;
    
    // Establish the bijection between rowI and rowIPairs
    assert forall y :: y in rowI <==> (i, y) in rowIPairs;
    assert forall p :: p in rowIPairs ==> p.0 == i && 1 <= p.1 <= n && (i * i + p.1 * p.1) % m == 0;
    assert rowIPairs == set y | y in rowI :: (i, y);
    
    // Now prove cardinality equality
    assert |rowIPairs| == |rowI|;
    
    assert setWithI == setBeforeI + rowIPairs;
    assert setBeforeI !! rowIPairs;
  }
}

lemma FinalRowCountLemma(n: int, m: int, i: int, rowCount: int)
  requires 1 <= n && 1 <= m
  requires 1 <= i <= n
  requires rowCount == |set y | 1 <= y < n + 1 && (i * i + y * y) % m == 0 :: y|
  ensures rowCount == |set y | 1 <= y <= n && (i * i + y * y) % m == 0 :: y|
{
  var s1 := set y | 1 <= y < n + 1 && (i * i + y * y) % m == 0 :: y;
  var s2 := set y | 1 <= y <= n && (i * i + y * y) % m == 0 :: y;
  assert s1 == s2;
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
    
    assert j == n + 1;
    FinalRowCountLemma(n, m, i, rowCount);
    assert rowCount == |set y | 1 <= y <= n && (i * i + y * y) % m == 0 :: y|;
    
    SetDecomposition(n, m, i);
    count := count + rowCount;
    i := i + 1;
  }
  
  assert i == n + 1;
  assert count == |set x, y | 1 <= x <= n && 1 <= y <= n && (x * x + y * y) % m == 0 :: (x, y)|;
  
  result := count;
}
// </vc-code>

