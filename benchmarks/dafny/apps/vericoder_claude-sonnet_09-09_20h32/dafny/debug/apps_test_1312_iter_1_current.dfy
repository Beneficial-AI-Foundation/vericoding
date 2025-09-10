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
lemma SumProperty(s: seq<int>, val1: int, val2: int, count1: int, count2: int)
  requires |s| == count1 + count2
  requires count(s, val1) == count1
  requires count(s, val2) == count2
  requires forall i :: 0 <= i < |s| ==> s[i] == val1 || s[i] == val2
  ensures sum(s) == count1 * val1 + count2 * val2
{
  if |s| == 0 {
  } else {
    if s[0] == val1 {
      SumProperty(s[1..], val1, val2, count1 - 1, count2);
    } else {
      SumProperty(s[1..], val1, val2, count1, count2 - 1);
    }
  }
}

lemma CountAppend(s1: seq<int>, s2: seq<int>, val: int)
  ensures count(s1 + s2, val) == count(s1, val) + count(s2, val)
{
  if |s1| == 0 {
  } else {
    CountAppend(s1[1..], s2, val);
  }
}

lemma SumAppend(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
  } else {
    SumAppend(s1[1..], s2);
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
  var larger_count := remainder;
  var smaller_count := m - remainder;
  
  var smaller_part := seq(smaller_count, i => base);
  var larger_part := seq(larger_count, i => base + 1);
  
  result := smaller_part + larger_part;
  
  // Prove sum property
  SumAppend(smaller_part, larger_part);
  SumProperty(smaller_part, base, base + 1, smaller_count, 0);
  SumProperty(larger_part, base, base + 1, 0, larger_count);
  
  // Prove count properties
  CountAppend(smaller_part, larger_part, base);
  CountAppend(smaller_part, larger_part, base + 1);
}
// </vc-code>

