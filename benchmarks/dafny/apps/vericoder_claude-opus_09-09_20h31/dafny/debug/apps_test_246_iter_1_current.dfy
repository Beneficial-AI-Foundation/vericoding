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
lemma SetCardinality(n: int, s: int, i: int, count: int)
  requires n >= 1 && s >= 1
  requires 0 <= i <= n
  requires count == |set x | 1 <= x <= i && Check(x, s)|
  ensures count >= 0
  ensures count <= i
{
  var S := set x | 1 <= x <= i && Check(x, s);
  assert S <= set x | 1 <= x <= i;
  CardinalitySubset(S, set x | 1 <= x <= i);
}

lemma CardinalitySubset<T>(A: set<T>, B: set<T>)
  requires A <= B
  ensures |A| <= |B|
{
  // Dafny can often prove this automatically
}

lemma ExtendSet(n: int, s: int, i: int, count: int)
  requires n >= 1 && s >= 1
  requires 1 <= i < n
  requires count == |set x | 1 <= x <= i && Check(x, s)|
  ensures Check(i + 1, s) ==> |set x | 1 <= x <= i + 1 && Check(x, s)| == count + 1
  ensures !Check(i + 1, s) ==> |set x | 1 <= x <= i + 1 && Check(x, s)| == count
{
  var S := set x | 1 <= x <= i && Check(x, s);
  var S' := set x | 1 <= x <= i + 1 && Check(x, s);
  
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
  var i := 1;
  
  while i <= n
    invariant 1 <= i <= n + 1
    invariant count == |set x | 1 <= x < i && Check(x, s)|
    invariant count >= 0
    invariant count <= i - 1
  {
    if i < n + 1 {
      ExtendSet(n, s, i - 1, count);
    }
    
    if Check(i, s) {
      count := count + 1;
    }
    
    i := i + 1;
  }
  
  assert i == n + 1;
  assert count == |set x | 1 <= x < n + 1 && Check(x, s)|;
  assert count == |set x | 1 <= x <= n && Check(x, s)|;
  
  result := count;
}
// </vc-code>

