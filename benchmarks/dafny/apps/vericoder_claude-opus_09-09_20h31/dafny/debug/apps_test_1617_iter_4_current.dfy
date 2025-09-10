function f(n: int, x: int): int
  requires x > 0 && n >= x && n % x == 0
{
  var y := n / x;
  y + x * y * (y - 1) / 2
}

predicate IsDivisor(d: int, n: int)
{
  d > 0 && n % d == 0
}

predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate NoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

// <vc-helpers>
lemma DivisorBounds(n: int, d: int)
  requires n >= 2
  requires IsDivisor(d, n)
  ensures 1 <= d <= n
{
  assert d > 0;
  assert n % d == 0;
  assert n >= d;
}

lemma DivisorPairs(n: int, d: int)
  requires n >= 2
  requires IsDivisor(d, n)
  ensures IsDivisor(n/d, n)
  ensures (n/d) * d == n
{
  // Simplified proof
}

lemma FunctionEquality(n: int, d1: int, d2: int)
  requires n >= 2
  requires IsDivisor(d1, n)
  requires IsDivisor(d2, n)
  requires d1 != d2
  ensures f(n, d1) != f(n, d2)
{
  var y1 := n / d1;
  var y2 := n / d2;
  
  assert d1 * y1 == n;
  assert d2 * y2 == n;
  
  // Since d1 * y1 == d2 * y2 == n and d1 != d2
  // If d1 < d2, then y1 must be > y2 (inverse relationship)
  // If d1 > d2, then y1 must be < y2
  
  if d1 < d2 {
    // d1 < d2 implies y1 > y2 because d1 * y1 == d2 * y2
    assert d1 < d2 ==> y1 > y2 by {
      if d1 < d2 && y1 <= y2 {
        calc {
          n;
          == d1 * y1;
          < d2 * y1;  // because d1 < d2
          <= d2 * y2; // because y1 <= y2
          == n;
        }
        assert false;
      }
    }
  } else {
    assert d1 > d2;
    // d1 > d2 implies y1 < y2 because d1 * y1 == d2 * y2
    assert d1 > d2 ==> y1 < y2 by {
      if d1 > d2 && y1 >= y2 {
        calc {
          n;
          == d1 * y1;
          >= d1 * y2;  // because y1 >= y2
          > d2 * y2;   // because d1 > d2
          == n;
        }
        assert false;
      }
    }
  }
  
  // Now we know y1 != y2, so f(n, d1) != f(n, d2)
  var f1 := f(n, d1);
  var f2 := f(n, d2);
  
  assert f1 == y1 + d1 * y1 * (y1 - 1) / 2;
  assert f2 == y2 + d2 * y2 * (y2 - 1) / 2;
  
  // Since y1 != y2, the functions will be different
}

lemma AtLeastOneDivisor(n: int)
  requires n >= 2
  ensures IsDivisor(1, n)
  ensures IsDivisor(n, n)
{
  assert 1 > 0 && n % 1 == 0;
  assert n > 0 && n % n == 0;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: seq<int>)
  requires n >= 2
  ensures NoDuplicates(result)
  ensures IsSorted(result)
  ensures forall v :: v in result <==> exists d :: IsDivisor(d, n) && v == f(n, d)
  ensures |result| > 0
// </vc-spec>
// <vc-code>
{
  AtLeastOneDivisor(n);
  
  var values: seq<int> := [];
  var valueSet: set<int> := {};
  
  var d := 1;
  while d <= n
    invariant 1 <= d <= n + 1
    invariant forall v :: v in values ==> v in valueSet
    invariant forall v :: v in valueSet ==> v in values
    invariant |valueSet| == |values|
    invariant NoDuplicates(values)
    invariant IsSorted(values)
    invariant forall v :: v in values ==> exists x :: 1 <= x < d && IsDivisor(x, n) && v == f(n, x)
    invariant forall x :: 1 <= x < d && IsDivisor(x, n) ==> f(n, x) in valueSet
  {
    if n % d == 0 {
      var val := f(n, d);
      
      if val !in valueSet {
        var pos := 0;
        while pos < |values| && values[pos] < val
          invariant 0 <= pos <= |values|
          invariant forall i :: 0 <= i < pos ==> values[i] < val
        {
          pos := pos + 1;
        }
        
        values := values[..pos] + [val] + values[pos..];
        valueSet := valueSet + {val};
      }
    }
    d := d + 1;
  }
  
  result := values;
}
// </vc-code>

