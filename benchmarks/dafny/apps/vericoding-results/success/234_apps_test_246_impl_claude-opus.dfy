function SumOfDigits(x: int): int
  requires x >= 0
  decreases x
{
  if x == 0 then 0
  else (x % 10) + SumOfDigits(x / 10)
}

function Check(x: int, s: int): bool
  requires x >= 0
{
  x - SumOfDigits(x) >= s
}

// <vc-helpers>
lemma IntRangeCardinality(i: int)
  requires i >= 0
  ensures |set x {:trigger 1 <= x <= i} | 1 <= x <= i| == if i >= 1 then i else 0
{
  if i == 0 {
    assert (set x {:trigger 1 <= x <= 0} | 1 <= x <= 0) == {};
  } else if i == 1 {
    assert (set x {:trigger 1 <= x <= 1} | 1 <= x <= 1) == {1};
  } else {
    IntRangeCardinality(i - 1);
    var S := set x {:trigger 1 <= x <= i} | 1 <= x <= i;
    var S' := set x {:trigger 1 <= x <= i - 1} | 1 <= x <= i - 1;
    assert S == S' + {i};
    assert i !in S';
    assert |S| == |S'| + 1;
  }
}

lemma SetCardinality(n: int, s: int, i: int, count: int)
  requires n >= 1 && s >= 1
  requires 0 <= i <= n
  requires count == |set x {:trigger Check(x, s)} | 1 <= x <= i && Check(x, s)|
  ensures count >= 0
  ensures count <= i
{
  var S := set x {:trigger Check(x, s)} | 1 <= x <= i && Check(x, s);
  var B := set x {:trigger 1 <= x <= i} | 1 <= x <= i;
  assert S <= B;
  
  if i == 0 {
    assert S == {};
    assert B == {};
    assert count == 0;
  } else {
    IntRangeCardinality(i);
    assert |B| == i;
    CardinalitySubset(S, B);
    assert |S| <= |B|;
    assert |S| <= i;
  }
}

lemma CardinalitySubset<T>(A: set<T>, B: set<T>)
  requires A <= B
  ensures |A| <= |B|
{
  if A == {} {
    assert |A| == 0;
    assert |A| <= |B|;
  } else if A == B {
    assert |A| == |B|;
  } else {
    var x :| x in B && x !in A;
    var B' := B - {x};
    assert A <= B';
    assert |B| == |B'| + 1;
    CardinalitySubset(A, B');
  }
}

lemma ExtendSet(n: int, s: int, i: int, count: int)
  requires n >= 1 && s >= 1
  requires 0 <= i < n
  requires count == |set x {:trigger Check(x, s)} | 1 <= x <= i && Check(x, s)|
  ensures Check(i + 1, s) ==> |set x {:trigger Check(x, s)} | 1 <= x <= i + 1 && Check(x, s)| == count + 1
  ensures !Check(i + 1, s) ==> |set x {:trigger Check(x, s)} | 1 <= x <= i + 1 && Check(x, s)| == count
{
  var S := set x {:trigger Check(x, s)} | 1 <= x <= i && Check(x, s);
  var S' := set x {:trigger Check(x, s)} | 1 <= x <= i + 1 && Check(x, s);
  
  if Check(i + 1, s) {
    assert S' == S + {i + 1};
    assert i + 1 !in S;
  } else {
    assert S' == S;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: int) returns (result: int)
  requires n >= 1 && s >= 1
  ensures result >= 0
  ensures result <= n
  ensures result == |set x | 1 <= x <= n && Check(x, s)|
// </vc-spec>
// <vc-code>
{
  var count := 0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant count == |set x {:trigger Check(x, s)} | 1 <= x <= i && Check(x, s)|
    invariant count >= 0
    invariant count <= i
  {
    ExtendSet(n, s, i, count);
    
    if Check(i + 1, s) {
      count := count + 1;
    }
    
    i := i + 1;
  }
  
  assert i == n;
  assert count == |set x {:trigger Check(x, s)} | 1 <= x <= n && Check(x, s)|;
  
  result := count;
}
// </vc-code>

