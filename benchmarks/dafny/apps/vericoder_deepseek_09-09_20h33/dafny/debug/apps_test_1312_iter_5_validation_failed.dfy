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
lemma DistributionProperties(n: int, m: int)
  requires ValidInput(n, m)
  ensures m - (n % m) >= 0
  ensures n % m >= 0
{
}

lemma CountLemma(s: seq<int>, val1: int, val2: int)
  requires val1 != val2
  ensures count(s, val1) + count(s, val2) <= |s|
{
}

lemma CountUpdate(s: seq<int>, val: int, x: int)
  ensures count(s + [x], val) == count(s, val) + (if x == val then 1 else 0)
{
}

lemma SumUpdate(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
}

lemma SumLemma(s: seq<int>, base: int, i: int, remainder: int)
  requires |s| == i
  requires sum(s) == base * i + (if i <= remainder then i else remainder)
  requires count(s, base) == (if i <= remainder then 0 else i - remainder)
  requires count(s, base + 1) == (if i <= remainder then i else remainder)
  ensures sum(s) + base == base * (i + 1) + (if i + 1 <= remainder then i + 1 else remainder)
  decreases |s|
{
  calc {
    sum(s) + base;
    == { assume true; }
    base * i + (if i <= remainder then i else remainder) + base;
    == { 
      if i <= remainder {
        assert base * i + base + i == base * (i + 1) + i;
      } else {
        assert base * i + base + remainder == base * (i + 1) + remainder;
      }
    }
    base * (i + 1) + (if i + 1 <= remainder then i + 1 else remainder);
  }
}

lemma CountLemmaBase(s: seq<int>, base: int, i: int, remainder: int, x: int)
  requires |s| == i
  requires count(s, base) == (if i <= remainder then 0 else i - remainder)
  requires count(s, base + 1) == (if i <= remainder then i else remainder)
  requires x == base
  requires i >= remainder
  ensures count(s + [x], base) == (if i + 1 <= remainder then 0 else (i + 1) - remainder)
  ensures count(s + [x], base + 1) == (if i + 1 <= remainder then i + 1 else remainder)
{
  calc {
    count(s + [base], base);
    == { CountUpdate(s, base, base) }
    count(s, base) + 1;
    == { 
      if i <= remainder {
        assert false; // Contradiction with i >= remainder
      } else {
        assert count(s, base) == i - remainder;
      }
    }
    (i - remainder) + 1;
    ==
    (i + 1) - remainder;
  }
  calc {
    count(s + [base], base + 1);
    == { CountUpdate(s, base + 1, base) }
    count(s, base + 1) + 0;
    ==
    count(s, base + 1);
    ==
    remainder;
  }
}

lemma CountLemmaBasePlusOne(s: seq<int>, base: int, i: int, remainder: int, x: int)
  requires |s| == i
  requires count(s, base) == (if i <= remainder then 0 else i - remainder)
  requires count(s, base + 1) == (if i <= remainder then i else remainder)
  requires x == base + 1
  requires i < remainder
  ensures count(s + [x], base) == (if i + 1 <= remainder then 0 else (i + 1) - remainder)
  ensures count(s + [x], base + 1) == (if i + 1 <= remainder then i + 1 else remainder)
{
  calc {
    count(s + [base + 1], base);
    == { CountUpdate(s, base, base + 1) }
    count(s, base) + 0;
    ==
    count(s, base);
    ==
    0;
  }
  calc {
    count(s + [base + 1], base + 1);
    == { CountUpdate(s, base + 1, base + 1) }
    count(s, base + 1) + 1;
    ==
    i + 1;
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
  result := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |result| == i
    invariant sum(result) == base * i + (if i <= remainder then i else remainder)
    invariant count(result, base) == (if i <= remainder then 0 else i - remainder)
    invariant count(result, base + 1) == (if i <= remainder then i else remainder)
    decreases m - i
  {
    if i < remainder {
      result := result + [base + 1];
      SumUpdate(result[0..|result|-1], base + 1);
      CountUpdate(result[0..|result|-1], base, base + 1);
      CountUpdate(result[0..|result|-1], base + 1, base + 1);
    } else {
      result := result + [base];
      SumUpdate(result[0..|result|-1], base);
      CountUpdate(result[0..|result|-1], base, base);
      CountUpdate(result[0..|result|-1], base + 1, base);
    }
    i := i + 1;
  }
}
// </vc-code>

