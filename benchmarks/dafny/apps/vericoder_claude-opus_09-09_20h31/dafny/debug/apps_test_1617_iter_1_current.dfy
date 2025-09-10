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
  assert d > 0;
  assert n % d == 0;
  var q := n / d;
  assert q * d == n;
  assert q > 0;
  assert n % q == 0;
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
  
  if d1 < d2 {
    assert y1 > y2;
  } else {
    assert d1 > d2;
    assert y1 < y2;
  }
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
  
  var divisors: seq<int> := [];
  var values: seq<int> := [];
  
  var d := 1;
  while d <= n
    invariant 1 <= d <= n + 1
    invariant forall i :: 0 <= i < |divisors| ==> IsDivisor(divisors[i], n)
    invariant forall i :: 0 <= i < |divisors| ==> 1 <= divisors[i] < d
    invariant forall x :: 1 <= x < d && IsDivisor(x, n) ==> x in divisors
    invariant |divisors| == |values|
    invariant forall i :: 0 <= i < |values| ==> values[i] == f(n, divisors[i])
    invariant NoDuplicates(divisors)
    invariant IsSorted(divisors)
    invariant NoDuplicates(values)
    invariant IsSorted(values)
  {
    if n % d == 0 {
      assert IsDivisor(d, n);
      var val := f(n, d);
      
      divisors := divisors + [d];
      
      // Find insertion position for val to maintain sorted order
      var pos := 0;
      while pos < |values| && values[pos] < val
        invariant 0 <= pos <= |values|
        invariant forall i :: 0 <= i < pos ==> values[i] < val
      {
        pos := pos + 1;
      }
      
      if pos < |values| && values[pos] == val {
        // Value already exists, don't add duplicate
        divisors := divisors[..|divisors|-1];
      } else {
        // Insert val at position pos
        values := values[..pos] + [val] + values[pos..];
        
        // Prove that values remains sorted and without duplicates
        assert IsSorted(values[..pos]);
        assert IsSorted(values[pos+1..]);
        assert forall i :: 0 <= i < pos ==> values[i] < val;
        assert forall i :: pos + 1 < |values| ==> val <= values[i];
      }
    }
    d := d + 1;
  }
  
  assert |divisors| > 0;
  assert |values| > 0;
  
  result := values;
}
// </vc-code>

