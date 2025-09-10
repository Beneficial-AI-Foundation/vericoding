function sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + sum(s[1..])
}

predicate isDistinct(s: seq<int>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate isSorted(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i + 1]
}

predicate isValidCombination(combo: seq<int>, k: int, n: int)
{
    |combo| == k &&
    sum(combo) == n &&
    (forall j :: 0 <= j < |combo| ==> 1 <= combo[j] <= 9) &&
    isDistinct(combo) &&
    isSorted(combo)
}

predicate isValidExtension(temp: seq<int>, combo: seq<int>, k: int, n: int, start: int)
{
    |combo| == k &&
    sum(combo) == n &&
    (forall j :: 0 <= j < |combo| ==> 1 <= combo[j] <= 9) &&
    isDistinct(combo) &&
    isSorted(combo) &&
    |combo| >= |temp| &&
    (forall i :: 0 <= i < |temp| ==> temp[i] == combo[i]) &&
    (forall i :: |temp| <= i < |combo| ==> combo[i] >= start)
}

// <vc-helpers>
lemma LemmaSumAppend(s: seq<int>, t: seq<int>)
  ensures sum(s + t) == sum(s) + sum(t)
{
  if |s| == 0 {
    assert s + t == t;
    assert sum(s) == 0;
  } else {
    calc {
      sum(s + t);
      == { assert (s + t)[0] == s[0]; assert (s + t)[1..] == s[1..] + t; }
      s[0] + sum(s[1..] + t);
      == { LemmaSumAppend(s[1..], t); }
      s[0] + (sum(s[1..]) + sum(t));
      == 
      (s[0] + sum(s[1..])) + sum(t);
      ==
      sum(s) + sum(t);
    }
  }
}

lemma LemmaSumEmpty()
  ensures sum([]) == 0
{
}

lemma LemmaSumSingle(x: int)
  ensures sum([x]) == x
{
}

lemma LemmaSumRange(start: int, end: int)
  requires start <= end
  ensures sum([start..end]) == (start + end) * (end - start + 1) / 2
  decreases end - start
{
  if start == end {
    assert [start..end] == [start];
    LemmaSumSingle(start);
  } else {
    var mid := start + 1;
    assert [start..end] == [start] + [mid..end];
    LemmaSumAppend([start], [mid..end]);
    LemmaSumRange(mid, end);
  }
}

lemma LemmaIsSortedConcat(a: seq<int>, b: seq<int>)
  requires isSorted(a) && isSorted(b) && (|a| > 0 && |b| > 0 ==> a[|a|-1] < b[0])
  ensures isSorted(a + b)
{
  var s := a + b;
  forall i | 0 <= i < |s| - 1
    ensures s[i] < s[i + 1]
  {
    if i < |a| - 1 {
      assert s[i] == a[i] && s[i + 1] == a[i + 1];
    } else if i == |a| - 1 {
      assert s[i] == a[|a|-1] && s[i + 1] == b[0];
    } else {
      assert s[i] == b[i - |a|] && s[i + 1] == b[i - |a| + 1];
    }
  }
}

lemma LemmaIsDistinctConcat(a: seq<int>, b: seq<int>)
  requires isDistinct(a) && isDistinct(b) && (forall x :: x in a ==> !(x in b))
  ensures isDistinct(a + b)
{
  forall i, j | 0 <= i < j < |a + b|
    ensures (a + b)[i] != (a + b)[j]
  {
    if j < |a| {
      // Both in a
      assert (a + b)[i] == a[i] && (a + b)[j] == a[j];
    } else if i >= |a| {
      // Both in b
      assert (a + b)[i] == b[i - |a|] && (a + b)[j] == b[j - |a|];
    } else {
      // i in a, j in b
      assert (a + b)[i] == a[i] && (a + b)[j] == b[j - |a|];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method combinationSum3(k: int, n: int) returns (result: seq<seq<int>>)
    requires k > 0 && n > 0 && k <= 9
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == k
    ensures forall i :: 0 <= i < |result| ==> sum(result[i]) == n
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> 1 <= result[i][j] <= 9
    ensures forall i :: 0 <= i < |result| ==> isDistinct(result[i])
    ensures forall i :: 0 <= i < |result| ==> isSorted(result[i])
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    ensures forall combo :: isValidCombination(combo, k, n) ==> combo in result
    ensures forall combo :: combo in result ==> isValidCombination(combo, k, n)
// </vc-spec>
// <vc-code>
{
    var temp := [];
    var start := 1;
    var res: seq<seq<int>> := [];
    
    while true
        invariant |temp| <= k
        invariant forall i :: 0 <= i < |temp| ==> 1 <= temp[i] <= 9
        invariant isDistinct(temp)
        invariant isSorted(temp)
        invariant sum(temp) <= n
        invariant |temp| == 0 || temp[|temp|-1] < start
        invariant forall combo :: isValidExtension(temp, combo, k, n, start) ==> combo in res
        invariant forall combo :: combo in res ==> isValidCombination(combo, k, n)
        decreases k - |temp|, 10 - start
    {
        if |temp| == k {
            if sum(temp) == n {
                res := res + [temp];
            }
            if |temp| == 0 {
                break;
            }
            start := temp[|temp|-1] + 1;
            temp := temp[..|temp|-1];
        } else if start > 9 {
            if |temp| == 0 {
                break;
            }
            start := temp[|temp|-1] + 1;
            temp := temp[..|temp|-1];
        } else {
            var newSum := sum(temp) + start;
            if newSum <= n {
                temp := temp + [start];
            } else {
                start := start + 1;
            }
        }
    }
    
    result := res;
}
// </vc-code>

