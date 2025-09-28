// <vc-preamble>
function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define sortedness predicate */
predicate IsSorted(s: seq<int>) {
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

/* helper modified by LLM (iteration 5): insertion into a sequence (functional) */
function Insert(x: int, s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [x]
  else if x <= s[0] then [x] + s
  else [s[0]] + Insert(x, s[1..])
}

/* helper modified by LLM (iteration 5): tail of a sorted sequence is sorted (requires non-empty) */
lemma LemmaSortedTail(s: seq<int>)
  requires IsSorted(s)
  requires |s| > 0
  ensures IsSorted(s[1..])
{
  forall i, j | 0 <= i < j < |s[1..]|
    ensures s[1..][i] <= s[1..][j]
  {
    assert |s[1..]| == |s| - 1;
    assert 0 <= i + 1 < j + 1 < |s|;
    assert s[i + 1] <= s[j + 1]; // from IsSorted(s)
    assert s[1..][i] == s[i + 1];
    assert s[1..][j] == s[j + 1];
  }
}

/* helper modified by LLM (iteration 5): head of Insert is min(x, head(t)) when t is non-empty */
lemma Lemma_InsertHead(x: int, t: seq<int>)
  requires |t| > 0
  ensures Insert(x, t)[0] == (if x <= t[0] then x else t[0])
{
  if x <= t[0] {
    assert Insert(x, t) == [x] + t;
    assert Insert(x, t)[0] == x;
  } else {
    assert Insert(x, t) == [t[0]] + Insert(x, t[1..]);
    assert Insert(x, t)[0] == t[0];
  }
}

/* helper modified by LLM (iteration 5): prepend preserves sortedness if head is small enough */
lemma LemmaSortedPrependHead(v: int, t: seq<int>)
  requires IsSorted(t)
  requires |t| == 0 || v <= t[0]
  ensures IsSorted([v] + t)
{
  if |t| == 0 {
  } else {
    forall i, j | 0 <= i < j < |[v] + t|
      ensures ([v] + t)[i] <= ([v] + t)[j]
    {
      if i == 0 {
        var k := j - 1;
        assert 0 <= k < |t|;
        if k == 0 {
          assert v <= t[0];
          assert ([v] + t)[0] == v;
          assert ([v] + t)[j] == t[0];
          assert ([v] + t)[0] <= ([v] + t)[j];
        } else {
          assert 0 <= 0 < k < |t|;
          assert t[0] <= t[k];
          assert v <= t[0];
          assert v <= t[k];
          assert ([v] + t)[0] == v;
          assert ([v] + t)[j] == t[k];
          assert ([v] + t)[0] <= ([v] + t)[j];
        }
      } else {
        var i0 := i - 1;
        var j0 := j - 1;
        assert 0 <= i0 < j0 < |t|;
        assert t[i0] <= t[j0];
        assert ([v] + t)[i] == t[i0];
        assert ([v] + t)[j] == t[j0];
        assert ([v] + t)[i] <= ([v] + t)[j];
      }
    }
  }
}

/* helper modified by LLM (iteration 5): Insert preserves sortedness of a sorted tail */
lemma InsertPreservesSorted(x: int, t: seq<int>)
  requires IsSorted(t)
  ensures IsSorted(Insert(x, t))
  decreases |t|
{
  if |t| == 0 {
  } else if x <= t[0] {
    LemmaSortedPrependHead(x, t);
  } else {
    LemmaSortedTail(t);
    InsertPreservesSorted(x, t[1..]);
    if |t| == 1 {
      assert Insert(x, t[1..]) == [x];
      assert (Insert(x, t[1..]))[0] == x;
      assert t[0] <= x;
    } else {
      Lemma_InsertHead(x, t[1..]);
      assert t[1..][0] == t[1];
      assert 0 <= 0 < 1 < |t|;
      assert t[0] <= t[1];
      assert t[0] <= x;
      assert t[0] <= (if x <= t[1] then x else t[1]);
      assert t[0] <= (Insert(x, t[1..]))[0];
    }
    LemmaSortedPrependHead(t[0], Insert(x, t[1..]));
  }
}

/* helper modified by LLM (iteration 5): length of Insert result */
lemma InsertLength(x: int, s: seq<int>)
  ensures |Insert(x, s)| == |s| + 1
  decreases |s|
{
  if |s| == 0 {
  } else if x <= s[0] {
    assert |[x] + s| == 1 + |s|;
  } else {
    InsertLength(x, s[1..]);
    assert |[s[0]] + Insert(x, s[1..])| == 1 + |Insert(x, s[1..])|;
    assert |s[1..]| == |s| - 1;
    assert |Insert(x, s[1..])| == |s[1..]| + 1;
  }
}

/* helper modified by LLM (iteration 5): multiset of Insert result */
lemma InsertMultiset(x: int, s: seq<int>)
  ensures multiset(Insert(x, s)) == multiset(s) + multiset([x])
  decreases |s|
{
  if |s| == 0 {
  } else if x <= s[0] {
    assert multiset([x] + s) == multiset([x]) + multiset(s);
  } else {
    InsertMultiset(x, s[1..]);
    assert multiset([s[0]] + Insert(x, s[1..])) == multiset([s[0]]) + multiset(Insert(x, s[1..]));
    assert multiset(Insert(x, s[1..])) == multiset(s[1..]) + multiset([x]);
    assert multiset([s[0]]) + multiset(s[1..]) == multiset([s[0]] + s[1..]);
    assert [s[0]] + s[1..] == s;
  }
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)

  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): insertion sort with explicit lemmas for length and multiset */
  var res: seq<int> := [];
  var i: int := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant IsSorted(res)
    invariant |res| == i
    invariant multiset(res) == multiset(s[..i])
    decreases |s| - i
  {
    var oldRes := res;
    InsertPreservesSorted(s[i], oldRes);
    assert IsSorted(Insert(s[i], oldRes));
    res := Insert(s[i], oldRes);
    assert res == Insert(s[i], oldRes);
    assert IsSorted(res);

    InsertLength(s[i], oldRes);
    assert |res| == |oldRes| + 1;

    InsertMultiset(s[i], oldRes);
    assert multiset(res) == multiset(oldRes) + multiset([s[i]]);
    assert s[..i+1] == s[..i] + [s[i]];
    assert multiset(res) == multiset(s[..i+1]);

    i := i + 1;
  }
  sorted := res;
}
// </vc-code>
