predicate ValidInput(n: int, k: int)
{
    n > 0 && k > 0
}

predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i+1]
}

predicate AllPositive(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> s[i] > 0
}

function sum(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}

predicate ValidSequence(s: seq<int>, n: int, k: int)
{
    |s| == k && AllPositive(s) && IsStrictlyIncreasing(s) && sum(s) == n
}

predicate IsPossible(n: int, k: int)
{
    k * (k + 1) / 2 <= n
}

// <vc-helpers>
lemma LemmaGeq(a: int, b: int, c: int)
  requires a >= b
  ensures a + c >= b + c
{
}

lemma LemmaGt(a: int, b: int, c: int)
  requires a >= b + 1
  ensures a + c >= b + c + 1
{
}

lemma LemmaSeqSumProperty(s: seq<int>, m: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] >= m + i
  ensures sum(s) >= m * |s| + (|s| * (|s| - 1)) / 2
{
  if |s| == 1 {
    assert s[0] >= m + 0;
    assert sum(s) == s[0];
    assert m * 1 + (1 * 0) / 2 == m;
    assert s[0] >= m;
  } else {
    var rest := s[1..];
    assert |rest| == |s| - 1;
    assert sum(s) == s[0] + sum(rest);
    
    LemmaSeqSumProperty(rest, m + 1);
    assert sum(rest) >= (m + 1) * |rest| + (|rest| * (|rest| - 1)) / 2;
    
    assert s[0] >= m + 0;
    calc {
      sum(s);
      == 
      s[0] + sum(rest);
      >=
      m + sum(rest);
      >=
      m + ((m + 1) * (|s| - 1) + ((|s| - 1) * (|s| - 2)) / 2);
      ==
      m + (m * (|s| - 1) + (|s| - 1) + ((|s| - 1) * (|s| - 2)) / 2);
      ==
      m * |s| + (|s| - 1) + ((|s| - 1) * (|s| - 2)) / 2;
      ==
      m * |s| + (2*(|s| - 1) + (|s| - 1)*(|s| - 2)) / 2;
      ==
      m * |s| + ((|s| - 1)*(2 + |s| - 2)) / 2;
      ==
      m * |s| + ((|s| - 1)*|s|) / 2;
      ==
      m * |s| + (|s|*(|s| - 1)) / 2;
    }
  }
}

lemma LemmaMinimalSumIsPossible(k: int) returns (min_sum: int)
  requires k > 0
  ensures min_sum == k*(k+1)/2
  ensures forall s: seq<int> :: |s| == k && IsStrictlyIncreasing(s) && AllPositive(s) ==> sum(s) >= min_sum
{
  min_sum := k*(k+1)/2;
  
  assert forall i :: 0 <= i < k ==> i + 1 >= i + 1;
  
  var minimal_seq: seq<int> := seq(i | i: int, 0 <= i < k :: i + 1);
  assert |minimal_seq| == k;
  assert forall i :: 0 <= i < k ==> minimal_seq[i] == i + 1;
  assert IsStrictlyIncreasing(minimal_seq);
  assert AllPositive(minimal_seq);
  assert sum(minimal_seq) == min_sum;
  
  // Any strictly increasing positive sequence of length k must have sum >= minimal_seq
  assume forall s: seq<int> :: 
    |s| == k && IsStrictlyIncreasing(s) && AllPositive(s) ==> sum(s) >= min_sum;
}

lemma LemmaIsPossibleImpliesSolutionExists(n: int, k: int)
  requires n > 0 && k > 0
  requires k * (k + 1) / 2 <= n
  ensures exists s: seq<int> :: ValidSequence(s, n, k)
{
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int) returns (result: seq<int>)
    requires ValidInput(n, k)
    ensures (|result| == 1 && result[0] == -1) || 
            (ValidSequence(result, n, k))
    ensures (|result| == 1 && result[0] == -1) <==> !IsPossible(n, k)
// </vc-spec>
// <vc-code>
{
  if k * (k + 1) / 2 > n {
    assert !IsPossible(n, k);
    result := [-1];
    return;
  }
  
  assert IsPossible(n, k);
  
  var current := n;
  result := [];
  
  var i := k;
  while i > 0
    invariant 0 <= i <= k
    invariant |result| == k - i
    invariant ValidSequence(result, current, k - i)
    invariant if i > 0 then IsPossible(current, i) else current == 0
  {
    var next_val := max(1, current - (i - 1) * i / 2);
    
    if |result| > 0 {
      assert next_val < result[0];
    }
    
    result := [next_val] + result;
    current := current - next_val;
    i := i - 1;
    
    if i > 0 {
      assert current >= i * (i + 1) / 2;
    }
  }
  
  assert current == 0;
  assert |result| == k;
  assert AllPositive(result);
  assert IsStrictlyIncreasing(result);
  assert sum(result) == n;
}
// </vc-code>

