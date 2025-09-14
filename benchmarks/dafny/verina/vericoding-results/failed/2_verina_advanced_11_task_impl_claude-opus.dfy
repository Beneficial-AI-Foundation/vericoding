// <vc-preamble>
function CountOccurrences(x: int, lst: seq<int>): nat
{
    |set i | 0 <= i < |lst| && lst[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed cardinality lemmas and bounds */
function Candidate(lst: seq<int>, i: int, count: int, cand: int): (int, int)
  requires 0 <= i <= |lst|
  decreases |lst| - i
{
  if i == |lst| then
    (cand, count)
  else if count == 0 then
    Candidate(lst, i + 1, 1, lst[i])
  else if lst[i] == cand then
    Candidate(lst, i + 1, count + 1, cand)
  else
    Candidate(lst, i + 1, count - 1, cand)
}

function CountOccurrencesUpTo(x: int, lst: seq<int>, j: int): nat
  requires 0 <= j <= |lst|
  ensures CountOccurrencesUpTo(x, lst, j) <= j
{
  var s := set k | 0 <= k < j && lst[k] == x;
  CardinalityBound(s, j);
  |s|
}

lemma CardinalityBound(s: set<int>, j: int)
  requires s == set k | 0 <= k < j && k in s
  ensures |s| <= j
{
  if j == 0 {
    assert s == {};
  } else if j > 0 {
    var all := set k | 0 <= k < j;
    assert s <= all;
    if j < 1000000 {
      CardinalitySubset(s, all);
    } else {
      assert |s| <= |all|;
      assert |all| == j;
    }
  }
}

lemma CardinalitySubset(s: set<int>, t: set<int>)
  requires s <= t
  requires |t| < 1000000
  ensures |s| <= |t|
{
  if |s| > |t| {
    var x :| x in s && x !in t;
    assert false;
  }
}

lemma CountOccurrencesComplete(x: int, lst: seq<int>)
  ensures CountOccurrences(x, lst) == CountOccurrencesUpTo(x, lst, |lst|)
{
}

lemma MajorityElementUnique(lst: seq<int>, x: int, y: int)
  requires CountOccurrences(x, lst) > |lst| / 2
  requires CountOccurrences(y, lst) > |lst| / 2
  ensures x == y
{
  if x != y {
    var n := |lst|;
    var sx := set i | 0 <= i < n && lst[i] == x;
    var sy := set i | 0 <= i < n && lst[i] == y;
    assert sx * sy == {};
    var sxy := sx + sy;
    assert |sxy| == |sx| + |sy|;
    assert |sx| > n / 2;
    assert |sy| > n / 2;
    assert |sxy| > n;
    var all := set i | 0 <= i < n;
    assert sxy <= all;
    CardinalityOfRange(n);
    assert |all| == n;
    if n < 1000000 {
      CardinalitySubset(sxy, all);
      assert |sxy| <= n;
      assert false;
    } else {
      assert |sxy| <= |all|;
      assert |sxy| <= n;
      assert false;
    }
  }
}

lemma CardinalityOfRange(n: int)
  requires n >= 0
  ensures |set i | 0 <= i < n| == n
{
  if n == 0 {
    assert set i | 0 <= i < n == {};
  } else {
    var s := set i | 0 <= i < n;
    var s' := set i | 0 <= i < n-1;
    assert s == s' + {n-1};
    CardinalityOfRange(n-1);
  }
}

lemma BoyerMooreCorrect(lst: seq<int>)
  requires |lst| > 0
  ensures var (c, cnt) := Candidate(lst, 0, 0, 0);
          CountOccurrences(c, lst) > |lst| / 2 ==> 
          forall x :: CountOccurrences(x, lst) > |lst| / 2 ==> x == c
{
  var (c, cnt) := Candidate(lst, 0, 0, 0);
  if CountOccurrences(c, lst) > |lst| / 2 {
    forall x | CountOccurrences(x, lst) > |lst| / 2
    ensures x == c
    {
      MajorityElementUnique(lst, c, x);
    }
  }
}

lemma CountOccurrencesUpToNext(x: int, lst: seq<int>, j: int)
  requires 0 <= j < |lst|
  ensures CountOccurrencesUpTo(x, lst, j + 1) == 
          CountOccurrencesUpTo(x, lst, j) + (if lst[j] == x then 1 else 0)
{
  var s1 := set k | 0 <= k < j && lst[k] == x;
  var s2 := set k | 0 <= k < j + 1 && lst[k] == x;
  if lst[j] == x {
    assert s2 == s1 + {j};
  } else {
    assert s2 == s1;
  }
}
// </vc-helpers>

// <vc-spec>
method FindMajorityElement(lst: array<int>) returns (result: int)
    ensures var lst_seq := lst[..];
            var n := |lst_seq|;
            var majority := CountOccurrences(result, lst_seq) > n / 2 && 
                          forall x :: CountOccurrences(x, lst_seq) <= n / 2 || x == result;
            (result == -1 ==> forall x :: CountOccurrences(x, lst_seq) <= n / 2) &&
            (result != -1 ==> majority)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed proof by using Boyer-Moore correctness directly */
{
  if lst.Length == 0 {
    result := -1;
    return;
  }
  
  var lst_seq := lst[..];
  var (cand, count) := Candidate(lst_seq, 0, 0, 0);
  
  BoyerMooreCorrect(lst_seq);
  
  var occurrences := 0;
  var j := 0;
  while j < lst.Length
    invariant 0 <= j <= lst.Length
    invariant occurrences == CountOccurrencesUpTo(cand, lst_seq, j)
  {
    CountOccurrencesUpToNext(cand, lst_seq, j);
    if lst[j] == cand {
      occurrences := occurrences + 1;
    }
    j := j + 1;
  }
  
  CountOccurrencesComplete(cand, lst_seq);
  assert occurrences == CountOccurrences(cand, lst_seq);
  
  if occurrences > lst.Length / 2 {
    result := cand;
    assert CountOccurrences(result, lst_seq) > lst.Length / 2;
    forall x | CountOccurrences(x, lst_seq) > lst.Length / 2
    ensures x == result
    {
      MajorityElementUnique(lst_seq, result, x);
    }
    assert forall x :: CountOccurrences(x, lst_seq) <= lst.Length / 2 || x == result;
  } else {
    result := -1;
    assert CountOccurrences(cand, lst_seq) <= lst.Length / 2;
    forall x
    ensures CountOccurrences(x, lst_seq) <= lst.Length / 2
    {
      if CountOccurrences(x, lst_seq) > lst.Length / 2 {
        assert CountOccurrences(cand, lst_seq) > lst.Length / 2 ==> forall y :: CountOccurrences(y, lst_seq) > lst.Length / 2 ==> y == cand by {
          BoyerMooreCorrect(lst_seq);
        }
        assert x == cand;
        assert false;
      }
    }
  }
}
// </vc-code>
