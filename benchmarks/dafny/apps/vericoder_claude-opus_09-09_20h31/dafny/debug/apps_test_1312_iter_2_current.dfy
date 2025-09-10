predicate ValidInput(n: int, m: int)
{
  n >= m > 0
}

function sum(s: seq<int>): int
{
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}

function count(s: seq<int>, val: int): int
{
  if |s| == 0 then 0 
  else (if s[0] == val then 1 else 0) + count(s[1..], val)
}

predicate OptimalDistribution(result: seq<int>, n: int, m: int)
  requires m > 0
{
  |result| == m &&
  (forall i :: 0 <= i < |result| ==> result[i] > 0) &&
  sum(result) == n &&
  (forall i :: 0 <= i < |result| ==> result[i] == n / m || result[i] == n / m + 1) &&
  count(result, n / m) == m - (n % m) &&
  count(result, n / m + 1) == n % m
}

// <vc-helpers>
lemma SumDistribution(result: seq<int>, n: int, m: int)
  requires m > 0
  requires |result| == m
  requires forall i :: 0 <= i < |result| ==> result[i] == n / m || result[i] == n / m + 1
  requires count(result, n / m) == m - (n % m)
  requires count(result, n / m + 1) == n % m
  ensures sum(result) == n
{
  if |result| == 0 {
    assert sum(result) == 0;
    assert n % m == 0;
    assert n == 0;
  } else {
    var rest := result[1..];
    assert |rest| == m - 1;
    
    if result[0] == n / m {
      assert count(rest, n / m) == count(result, n / m) - 1;
      assert count(rest, n / m + 1) == count(result, n / m + 1);
    } else {
      assert result[0] == n / m + 1;
      assert count(rest, n / m) == count(result, n / m);
      assert count(rest, n / m + 1) == count(result, n / m + 1) - 1;
    }
    
    var total_count_base := count(result, n / m);
    var total_count_plus := count(result, n / m + 1);
    assert total_count_base + total_count_plus == m;
    
    calc == {
      sum(result);
      result[0] + sum(rest);
      { SumByCount(result, n, m); }
      n;
    }
  }
}

lemma SumByCount(result: seq<int>, n: int, m: int)
  requires m > 0
  requires |result| == m
  requires forall i :: 0 <= i < |result| ==> result[i] == n / m || result[i] == n / m + 1
  requires count(result, n / m) == m - (n % m)
  requires count(result, n / m + 1) == n % m
  ensures sum(result) == n
{
  if |result| == 0 {
  } else {
    SumByCountHelper(result, n, m, 0);
  }
}

lemma SumByCountHelper(result: seq<int>, n: int, m: int, idx: int)
  requires m > 0
  requires |result| == m
  requires 0 <= idx <= |result|
  requires forall i :: 0 <= i < |result| ==> result[i] == n / m || result[i] == n / m + 1
  requires count(result, n / m) == m - (n % m)
  requires count(result, n / m + 1) == n % m
  ensures sum(result[idx..]) == (n / m) * count(result[idx..], n / m) + (n / m + 1) * count(result[idx..], n / m + 1)
  decreases |result| - idx
{
  if idx == |result| {
    assert result[idx..] == [];
    assert sum([]) == 0;
    assert count([], n / m) == 0;
    assert count([], n / m + 1) == 0;
  } else {
    var tail := result[idx+1..];
    SumByCountHelper(result, n, m, idx + 1);
    
    assert result[idx..] == [result[idx]] + tail;
    assert sum(result[idx..]) == result[idx] + sum(tail);
    
    if result[idx] == n / m {
      assert count(result[idx..], n / m) == 1 + count(tail, n / m);
      assert count(result[idx..], n / m + 1) == count(tail, n / m + 1);
    } else {
      assert result[idx] == n / m + 1;
      assert count(result[idx..], n / m) == count(tail, n / m);
      assert count(result[idx..], n / m + 1) == 1 + count(tail, n / m + 1);
    }
  }
  
  if idx == 0 {
    var base_count := count(result, n / m);
    var plus_count := count(result, n / m + 1);
    assert base_count == m - (n % m);
    assert plus_count == n % m;
    
    calc == {
      sum(result);
      (n / m) * base_count + (n / m + 1) * plus_count;
      (n / m) * (m - (n % m)) + (n / m + 1) * (n % m);
      (n / m) * m - (n / m) * (n % m) + (n / m) * (n % m) + (n % m);
      (n / m) * m + (n % m);
      n;
    }
  }
}

lemma CountAppend(s: seq<int>, val: int, x: int)
  ensures count(s + [x], val) == count(s, val) + (if x == val then 1 else 0)
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert count([x], val) == if x == val then 1 else 0;
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    CountAppend(s[1..], val, x);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (result: seq<int>)
  requires ValidInput(n, m)
  ensures OptimalDistribution(result, n, m)
// </vc-spec>
// <vc-code>
{
  var base := n / m;
  var remainder := n % m;
  var numBase := m - remainder;
  var numBasePlusOne := remainder;
  
  result := [];
  var i := 0;
  
  while i < numBase
    invariant 0 <= i <= numBase
    invariant |result| == i
    invariant forall j :: 0 <= j < |result| ==> result[j] == base
    invariant count(result, base) == i
    invariant count(result, base + 1) == 0
  {
    CountAppend(result, base, base);
    CountAppend(result, base + 1, base);
    result := result + [base];
    i := i + 1;
  }
  
  i := 0;
  while i < numBasePlusOne
    invariant 0 <= i <= numBasePlusOne
    invariant |result| == numBase + i
    invariant forall j :: 0 <= j < numBase ==> result[j] == base
    invariant forall j :: numBase <= j < |result| ==> result[j] == base + 1
    invariant count(result, base) == numBase
    invariant count(result, base + 1) == i
  {
    CountAppend(result, base, base + 1);
    CountAppend(result, base + 1, base + 1);
    result := result + [base + 1];
    i := i + 1;
  }
  
  assert |result| == numBase + numBasePlusOne == m;
  assert forall i :: 0 <= i < |result| ==> result[i] > 0;
  assert forall i :: 0 <= i < |result| ==> result[i] == base || result[i] == base + 1;
  assert count(result, base) == numBase == m - remainder;
  assert count(result, base + 1) == numBasePlusOne == remainder;
  
  SumDistribution(result, n, m);
}
// </vc-code>

