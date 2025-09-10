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
lemma CombineIneq(a: int, b: int)
  requires a >= 1
  requires b >= 1
  ensures comb2(a) + comb2(b) <= comb2(a + b - 1)
{
  // comb2(x) = x*(x-1)/2
  // comb2(a+b-1) - comb2(a) - comb2(b) = (a-1)*(b-1) >= 0
  calc {
    comb2(a + b - 1) - comb2(a) - comb2(b);
    == ((a + b - 1) * (a + b - 2) - a * (a - 1) - b * (b - 1)) / 2;
    == (2 * (a - 1) * (b - 1)) / 2;
    == (a - 1) * (b - 1);
  }
  assert (a - 1) * (b - 1) >= 0;
  assert comb2(a) + comb2(b) <= comb2(a + b - 1);
}

function SeqSum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + SeqSum(s[1..])
}

lemma SumComb2LeMax(s: seq<int>)
  requires |s| >= 1
  requires forall i :: 0 <= i < |s| ==> s[i] >= 1
  ensures (var n := SeqSum(s); var m := |s|; SeqSum([comb2(x) | x <- s]) <= comb2(n - m + 1))
  decreases |s|
{
  if |s| == 1 {
    // seq of one element: comb2(s[0]) <= comb2(s[0]) holds
  } else {
    var a := s[0];
    var b := s[1];
    CombineIneq(a, b);
    var newFirst := a + b - 1;
    var rest := s[2..];
    var newSeq := [newFirst] + rest;
    // newSeq length is |s|-1, and each element >= 1
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
    // Show sum comb2(s) <= sum comb2(newSeq)
    // comb2(a) + comb2(b) <= comb2(newFirst)
    assert comb2(a) + comb2(b) <= comb2(newFirst);
    // Now apply induction
    SumComb2LeMax(newSeq);
    // Combine inequalities: sum comb2(s) <= sum comb2(newSeq) <= comb2(SeqSum(newSeq) - |newSeq| + 1)
    // Note SeqSum(newSeq) = SeqSum(s) - 1 and |newSeq| = |s| - 1
    assert SeqSum(newSeq) == SeqSum(s) - 1;
    assert |newSeq| == |s| - 1;
  }
}

lemma Comb2NonNeg(x: int)
  requires x >= 0
  ensures comb2(x) >= 0
{
  // comb2(x) = x*(x-1)/2 >= 0 for x >= 0
  if x <= 1 {
    // comb2(0) = 0, comb2(1) = 0
  } else {
    assert x * (x - 1) >= 0;
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
  // k >= 1 because n >= m >= 1
  assert k >= 1;
  Comb2NonNeg(k);
  Comb2NonNeg(k + 1);
  Comb2NonNeg(n - m + 1);

  // Build the sequence representing the minimal distribution: p copies of (k+1), then m-p copies of k
  var s := [] : seq<int>;
  var i := 0;
  while i < p
    decreases p - i
  {
    s := s + [k + 1];
    i := i + 1;
  }
  i := p;
  while i < m
    decreases m - i
  {
    s := s + [k];
    i := i + 1;
  }
  assert |s| == m;
  assert forall j :: 0 <= j < |s| ==> s[j] >= 1
    by {
      var j := 0;
      while j < |s|
        decreases |s| - j
      {
        if
// </vc-code>

