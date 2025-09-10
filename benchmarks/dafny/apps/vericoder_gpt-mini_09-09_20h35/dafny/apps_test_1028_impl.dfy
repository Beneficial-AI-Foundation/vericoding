function comb2(n: int): int
  requires n >= 0
{
  n * (n - 1) / 2
}

predicate ValidInput(n: int, m: int)
{
  1 <= m <= n
}

function MinFriendshipPairs(n: int, m: int): int
  requires ValidInput(n, m)
{
  var k := n / m;
  var p := n % m;
  p * comb2(k + 1) + (m - p) * comb2(k)
}

function MaxFriendshipPairs(n: int, m: int): int
  requires ValidInput(n, m)
{
  comb2(n - m + 1)
}

// <vc-helpers>
function SeqSum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + SeqSum(s[1..])
}

function MapComb2(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [] else [comb2(s[0])] + MapComb2(s[1..])
}

lemma SeqSumAppend(s: seq<int>, v: int)
  ensures SeqSum(s + [v]) == SeqSum(s) + v
  decreases |s|
{
  if |s| == 0 {
    assert SeqSum([v]) == v;
  } else {
    var h := s[0];
    SeqSumAppend(s[1..], v);
    assert SeqSum(s) == h + SeqSum(s[1..]);
    assert SeqSum(s + [v]) == h + SeqSum(s[1..] + [v]);
    assert SeqSum(s + [v]) == h + (SeqSum(s[1..]) + v);
    assert SeqSum(s + [v]) == (h + SeqSum(s[1..])) + v;
    assert SeqSum(s + [v]) == SeqSum(s) + v;
  }
}

lemma MapComb2Append(s: seq<int>, v: int)
  ensures SeqSum(MapComb2(s + [v])) == SeqSum(MapComb2(s)) + comb2(v)
  decreases |s|
{
  if |s| == 0 {
    assert MapComb2([v]) == [comb2(v)];
    assert SeqSum([comb2(v)]) == comb2(v);
    assert SeqSum(MapComb2([])) == 0;
  } else {
    var h := s[0];
    MapComb2Append(s[1..], v);
    assert MapComb2(s) == [comb2(h)] + MapComb2(s[1..]);
    assert SeqSum(MapComb2(s)) == comb2(h) + SeqSum(MapComb2(s[1..]));
    assert MapComb2(s + [v]) == [comb2(h)] + MapComb2(s[1..] + [v]);
    assert SeqSum(MapComb2(s + [v])) == comb2(h) + SeqSum(MapComb2(s[1..] + [v]));
    assert SeqSum(MapComb2(s + [v])) == comb2(h) + (SeqSum(MapComb2(s[1..])) + comb2(v));
    assert SeqSum(MapComb2(s + [v])) == (comb2(h) + SeqSum(MapComb2(s[1..]))) + comb2(v);
    assert SeqSum(MapComb2(s + [v])) == SeqSum(MapComb2(s)) + comb2(v);
  }
}

lemma Comb2NonNeg(k: int)
  requires k >= 0
  ensures comb2(k) >= 0
{
  if k == 0 {
    assert comb2(0) == 0;
  } else {
    assert k - 1 >= 0;
    assert k * (k - 1) >= 0;
    assert comb2(k) == k * (k - 1) / 2;
    assert comb2(k) >= 0;
  }
}

lemma CombineIneq(a: int, b: int)
  requires a >= 1 && b >= 1
  ensures comb2(a) + comb2(b) <= comb2(a + b - 1)
{
  var lhs := a * (a - 1) + b * (b - 1);
  var rhs := (a + b - 1) * (a + b - 2);
  assert rhs - lhs == 2 * (a - 1) * (b - 1);
  assert (a - 1) * (b - 1) >= 0;
  assert rhs - lhs >= 0;
  assert 2 * comb2(a + b - 1) == rhs;
  assert 2 * (comb2(a) + comb2(b)) == lhs;
  assert 2 * comb2(a + b - 1) >= 2 * (comb2(a) + comb2(b));
  assert comb2(a + b - 1) >= comb2(a) + comb2(b);
}

lemma SumComb2LeMax(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures SeqSum(MapComb2(s)) <= comb2(SeqSum(s) - |s| + 1)
  decreases |s|
{
  if |s| == 0 {
    assert SeqSum(MapComb2([])) == 0;
    assert SeqSum([]) == 0;
    // comb2(1) == 0, so 0 <= comb2(1)
    assert comb2(1) == 0;
    assert 0 <= comb2(1);
  } else {
    var h := s[0];
    var rest := s[1..];
    SumComb2LeMax(rest);
    // define b = SeqSum(rest) - |rest| + 1
    var b := SeqSum(rest) - |rest| + 1;
    // each element in rest >= 1, so SeqSum(rest) >= |rest|, hence b >= 1
    assert b >= 1;
    // By induction SeqSum(MapComb2(rest)) <= comb2(b)
    assert SeqSum(MapComb2(rest)) <= comb2(b);
    // MapComb2(s) = [comb2(h)] + MapComb2(rest)
    assert MapComb2(s) == [comb2(h)] + MapComb2(rest);
    assert SeqSum(MapComb2(s)) == comb2(h) + SeqSum(MapComb2(rest));
    // combine inequalities
    CombineIneq(h, b);
    assert comb2(h) + SeqSum(MapComb2(rest)) <= comb2(h) + comb2(b);
    assert comb2(h) + comb2(b) <= comb2(h + b - 1);
    // compute h + b - 1 = SeqSum(s) - |s| + 1
    assert h + b - 1 == SeqSum(s) - |s| + 1;
    assert comb2(h + b - 1) == comb2(SeqSum(s) - |s| + 1);
    assert SeqSum(MapComb2(s)) <= comb2(SeqSum(s) - |s| + 1);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int) returns (min_pairs: int, max_pairs: int)
  requires ValidInput(n, m)
  ensures min_pairs >= 0
  ensures max_pairs >= 0
  ensures min_pairs <= max_pairs
  ensures min_pairs == MinFriendshipPairs(n, m)
  ensures max_pairs == MaxFriendshipPairs(n, m)
// </vc-spec>
// <vc-code>
{
  var k := n / m;
  var p := n % m;
  // compute min_pairs and max_pairs using definitions
  min_pairs := p * comb2(k + 1) + (m - p) * comb2(k);
  max_pairs := comb2(n - m + 1);

  // non-negativity proofs
  assert k >= 1;
  Comb2NonNeg(k);
  Comb2NonNeg(k + 1);
  Comb2NonNeg(n - m + 1);

  // Build the sequence representing the minimal distribution: p copies of (k+1), then m-p copies of k
  var s: seq<int> := [];
  var sum := 0;
  var sumComb := 0;
  var i := 0;
  while i < p
    decreases p - i
    invariant 0 <= i <= p
    invariant |s| == i
    invariant SeqSum(s) == sum
    invariant SeqSum(MapComb2(s)) == sumComb
  {
    s := s + [k + 1];
    sum := sum + (k + 1);
    sumComb := sumComb + comb2(k + 1);
    // maintain SeqSum and mapped SeqSum using helpers
    SeqSumAppend(s[0..|s|-1], k + 1); // helps Dafny know SeqSum(s) updated
    MapComb2Append(s[0..|s|-1], k + 1);
    i := i + 1;
  }
  i := p;
  while i < m
    decreases m - i
    invariant p <= i <= m
    invariant |s| == i
    invariant SeqSum(s) == sum
    invariant SeqSum(MapComb2(s)) == sumComb
  {
    s := s + [k];
    sum := sum + k;
    sumComb := sumComb + comb2(k);
    SeqSumAppend(s[0..|s|-1], k);
    MapComb2Append(s[0..|s|-1], k);
    i := i + 1;
  }
  assert |s| == m;
  assert SeqSum(s) == sum;
  assert sum == p * (k + 1) + (m - p) * k;
  assert n == m * k + p;
  assert SeqSum(s) == n;
  assert SeqSum(MapComb2(s)) == sumComb;
  assert sumComb == min_pairs;

  // each element >= 1
  assert forall j :: 0 <= j < |s| ==> s[j] >= 1
    by {
      var j := 0;
      while j < |s|
        decreases |s| - j
      {
        if j < p {
          assert s[j] == k + 1;
          assert k + 1 >= 1;
        } else {
          assert s[j] == k;
          assert k >= 1;
        }
        j := j + 1;
      }
    }

  // Apply lemma to show min_pairs <= max_pairs
  SumComb2LeMax(s);
  assert SeqSum(MapComb2(s)) <= comb2(SeqSum(s) - |s| + 1);
  assert SeqSum(s) == n;
  assert |s| == m;
  assert min_pairs <= max_pairs;
  // non-negativity of min_pairs and max_pairs
  assert min_pairs >= 0;
  assert max_pairs >= 0;
}
// </vc-code>

