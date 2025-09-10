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
lemma SeqSumAppend(s: seq<int>, v: int)
  ensures SeqSum(s + [v]) == SeqSum(s) + v
  decreases |s|
{
  if |s| == 0 {
    assert SeqSum([v]) == v;
  } else {
    // s = [h] + t
    var h := s[0];
    SeqSumAppend(s[1..], v);
    // SeqSum(s) == h + SeqSum(s[1..])
    assert SeqSum(s) == h + SeqSum(s[1..]);
    // SeqSum(s + [v]) == h + SeqSum(s[1..] + [v])
    assert SeqSum(s + [v]) == h + SeqSum(s[1..] + [v]);
    // by IH SeqSum(s[1..] + [v]) == SeqSum(s[1..]) + v
    assert SeqSum(s + [v]) == h + (SeqSum(s[1..]) + v);
    assert SeqSum(s + [v]) == (h + SeqSum(s[1..])) + v;
    assert SeqSum(s + [v]) == SeqSum(s) + v;
  }
}

lemma MapComb2Append(s: seq<int>, v: int)
  ensures SeqSum([comb2(x) | x <- s + [v]]) == SeqSum([comb2(x) | x <- s]) + comb2(v)
  decreases |s|
{
  if |s| == 0 {
    assert [comb2(x) | x <- s + [v]] == [comb2(v)];
    assert SeqSum([comb2(v)]) == comb2(v);
    assert SeqSum([comb2(x) | x <- s]) == 0;
  } else {
    var h := s[0];
    // [comb2(x) | x <- s + [v]] == [comb2(h)] + [comb2(x) | x <- s[1..] + [v]]
    // and [comb2(x) | x <- s] == [comb2(h)] + [comb2(x) | x <- s[1..]]
    MapComb2Append(s[1..], v);
    assert SeqSum([comb2(x) | x <- s]) == comb2(h) + SeqSum([comb2(x) | x <- s[1..]]);
    assert SeqSum([comb2(x) | x <- s + [v]]) == comb2(h) + SeqSum([comb2(x) | x <- s[1..] + [v]]);
    assert SeqSum([comb2(x) | x <- s + [v]]) == comb2(h) + (SeqSum([comb2(x) | x <- s[1..]]) + comb2(v));
    assert SeqSum([comb2(x) | x <- s + [v]]) == (comb2(h) + SeqSum([comb2(x) | x <- s[1..]])) + comb2(v);
    assert SeqSum([comb2(x) | x <- s + [v]]) == SeqSum([comb2(x) | x <- s]) + comb2(v);
  }
}

lemma SumComb2LeMax(s: seq<int>)
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures SeqSum([comb2(x) | x <- s]) <= comb2(SeqSum(s) - |s| + 1)
  decreases |s|
{
  if |s| == 1 {
    // For single element, equality holds
    assert SeqSum([comb2(x) | x <- s]) == comb2(s[0]);
    assert SeqSum(s) - |s| + 1 == s[0];
    assert SeqSum([comb2(x) | x <- s]) <= comb2(SeqSum(s) - |s| + 1);
  } else {
    var a := s[0];
    var b := s[1];
    CombineIneq(a, b);
    var newFirst := a + b - 1;
    var rest := s[2..];
    var newSeq := [newFirst] + rest;
    // newSeq length and non-negativity
    assert |newSeq| == |s| - 1;
    assert forall i :: 0 <= i < |newSeq| ==> newSeq[i] >= 1 by {
      var i := 0;
      while i < |newSeq|
        decreases |newSeq| - i
      {
        if i == 0 {
          assert newSeq[0] == newFirst;
          assert newFirst >= 1;
        } else {
          assert newSeq[i] == rest[i - 1];
          assert rest[i - 1] >= 1;
        }
        i := i + 1;
      }
    }

    // Decompose sum of comb2 over s
    assert [comb2(x) | x <- s] == [comb2(a), comb2(b)] + [comb2(x) | x <- rest];
    SeqSumAppend([comb2(a)], comb2(b));
    // SeqSum([comb2(a), comb2(b)]) == comb2(a) + comb2(b)
    assert SeqSum([comb2(a), comb2(b)]) == comb2(a) + comb2(b);
    // Thus
    assert SeqSum([comb2(x) | x <- s]) == comb2(a) + comb2(b) + SeqSum([comb2(x) | x <- rest]);

    // Decompose sum of comb2 over newSeq
    assert [comb2(x) | x <- newSeq] == [comb2(newFirst)] + [comb2(x) | x <- rest];
    assert SeqSum([comb2(x) | x <- newSeq]) == comb2(newFirst) + SeqSum([comb2(x) | x <- rest]);

    // Combine inequality comb2(a)+comb2(b) <= comb2(newFirst)
    assert comb2(a) + comb2(b) <= comb2(newFirst);
    assert comb2(a) + comb2(b) + SeqSum([comb2(x) | x <- rest]) <= comb2(newFirst) + SeqSum([comb2(x) | x <- rest]);
    assert SeqSum([comb2(x) | x <- s]) <= SeqSum([comb2(x) | x <- newSeq]);

    // Apply induction on newSeq
    SumComb2LeMax(newSeq);
    assert SeqSum([comb2(x) | x <- newSeq]) <= comb2(SeqSum(newSeq) - |newSeq| + 1);

    // SeqSum(newSeq) = SeqSum(s) - 1, and |newSeq| = |s| - 1
    assert SeqSum(newSeq) == SeqSum(s) - 1;
    assert |newSeq| == |s| - 1;

    // So comb2(SeqSum(newSeq) - |newSeq| + 1) = comb2(SeqSum(s) - |s| + 1)
    assert SeqSum([comb2(x) | x <- s]) <= comb2(SeqSum(s) - |s| + 1);
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
    invariant SeqSum([comb2(x) | x <- s]) == sumComb
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
    invariant SeqSum([comb2(x) | x <- s]) == sumComb
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
  assert SeqSum([comb2(x) | x <- s]) == sumComb;
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
  assert SeqSum([comb2(x) | x <- s]) <= comb2(SeqSum(s) - |s| + 1);
  assert SeqSum(s) == n;
  assert |s| == m;
  assert min_pairs <= max_pairs;
  // non-negativity of min_pairs and max_pairs
  assert min_pairs >= 0;
  assert max_pairs >= 0;
}
// </vc-code>

