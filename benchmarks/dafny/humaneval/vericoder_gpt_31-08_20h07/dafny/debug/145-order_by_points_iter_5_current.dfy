function digits_sum_pos(n: int): int
  requires n >= 0
{
  if n < 10 then n else digits_sum_pos(n / 10) + n % 10
}
function digits_sum(n: int): int {
  if n < 0 then digits_sum_pos(-n) else digits_sum_pos(n)
}

// <vc-helpers>
predicate SortedByDigitSum(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> digits_sum(s[i]) <= digits_sum(s[j])
}

function insert_by(x: int, t: seq<int>): seq<int>
  decreases |t|
{
  if |t| == 0 then [x]
  else if digits_sum(x) <= digits_sum(t[0]) then [x] + t
  else [t[0]] + insert_by(x, t[1..])
}

function sort_by(t: seq<int>): seq<int>
  decreases |t|
{
  if |t| == 0 then []
  else insert_by(t[0], sort_by(t[1..]))
}

lemma SortedImplyLe(u: seq<int>, i: int, j: int)
  requires SortedByDigitSum(u)
  requires 0 <= i < j < |u|
  ensures digits_sum(u[i]) <= digits_sum(u[j])
{}

lemma SortedTail(t: seq<int>)
  requires SortedByDigitSum(t)
  ensures SortedByDigitSum(t[1..])
{
  forall i, j | 0 <= i < j < |t[1..]| {
    assert 0 <= i + 1 < j + 1 < |t|;
    assert (t[1..])[i] == t[i+1];
    assert (t[1..])[j] == t[j+1];
    assert digits_sum(t[i+1]) <= digits_sum(t[j+1]) by {
      SortedImplyLe(t, i+1, j+1);
    }
  }
}

lemma SortedPrependIfLEFirst(b: int, u: seq<int>)
  requires |u| > 0
  requires SortedByDigitSum(u)
  requires digits_sum(b) <= digits_sum(u[0])
  ensures SortedByDigitSum([b] + u)
{
  forall i, j | 0 <= i < j < |[b] + u| {
    if i == 0 {
      var jj := j - 1;
      assert 0 <= jj < |u|;
      assert ([b] + u)[i] == b;
      assert ([b] + u)[j] == u[jj];
      if jj == 0 {
        assert digits_sum(u[0]) <= digits_sum(u[0]);
      } else {
        assert 0 <= 0 < jj < |u|;
        SortedImplyLe(u, 0, jj);
      }
      assert digits_sum(b) <= digits_sum(u[0]);
      assert digits_sum(b) <= digits_sum(u[jj]);
    } else {
      var ii := i - 1;
      var jj := j - 1;
      assert 0 <= ii < jj < |u|;
      assert ([b] + u)[i] == u[ii];
      assert ([b] + u)[j] == u[jj];
      SortedImplyLe(u, ii, jj);
    }
  }
}

lemma InsertByProps(x: int, u: seq<int>)
  ensures |insert_by(x, u)| == |u| + 1
  ensures multiset(insert_by(x, u)) == multiset([x] + u)
  decreases |u|
{
  if |u| == 0 {
    assert insert_by(x, u) == [x];
  } else if digits_sum(x) <= digits_sum(u[0]) {
    assert insert_by(x, u) == [x] + u;
  } else {
    assert insert_by(x, u) == [u[0]] + insert_by(x, u[1..]);
    InsertByProps(x, u[1..]);
    assert |insert_by(x, u)| == 1 + |insert_by(x, u[1..])|;
    assert |insert_by(x, u[1..])| == |u[1..]| + 1;
    assert |u| == 1 + |u[1..]|;
    assert |insert_by(x, u)| == |u| + 1;

    assert multiset(insert_by(x, u)) == multiset([u[0]] + insert_by(x, u[1..]));
    assert multiset([u[0]] + insert_by(x, u[1..])) == multiset([u[0]]) + multiset(insert_by(x, u[1..]));
    assert multiset(insert_by(x, u[1..])) == multiset([x] + u[1..]);
    assert multiset([x] + u) == multiset([x]) + multiset(u);
    assert multiset(u) == multiset([u[0]] + u[1..]) == multiset([u[0]]) + multiset(u[1..]);
    assert multiset([x]) + (multiset([u[0]]) + multiset(u[1..])) == multiset([u[0]]) + (multiset([x]) + multiset(u[1..]));
    assert multiset(insert_by(x, u)) == multiset([x] + u);
  }
}

lemma InsertBySorted(x: int, u: seq<int>)
  requires SortedByDigitSum(u)
  ensures SortedByDigitSum(insert_by(x, u))
  decreases |u|
{
  if |u| == 0 {
  } else if digits_sum(x) <= digits_sum(u[0]) {
    SortedPrependIfLEFirst(x, u);
  } else {
    SortedTail(u);
    InsertBySorted(x, u[1..]);
    var w := insert_by(x, u[1..]);
    InsertByProps(x, u[1..]);
    assert |w| > 0;
    if |u| == 1 {
      assert u[1..] == [];
      assert w == [x];
      assert digits_sum(u[0]) <= digits_sum(x);
    } else {
      assert (u[1..])[0] == u[1];
      if digits_sum(x) <= digits_sum(u[1]) {
        assert w == [x] + u[1..];
        assert w[0] == x;
        SortedImplyLe(u, 0, 1);
        assert digits_sum(u[0]) <= digits_sum(w[0]);
      } else {
        assert w == [u[1]] + insert_by(x, u[2..]);
        assert w[0] == u[1];
        SortedImplyLe(u, 0, 1);
        assert digits_sum(u[0]) <= digits_sum(w[0]);
      }
    }
    SortedPrependIfLEFirst(u[0], w);
  }
}

lemma SortByProps(t: seq<int>)
  ensures SortedByDigitSum(sort_by(t))
  ensures |sort_by(t)| == |t|
  ensures multiset(sort_by(t)) == multiset(t)
  decreases |t|
{
  if |t| == 0 {
    assert sort_by(t) == [];
  } else {
    SortByProps(t[1..]);
    InsertBySorted(t[0], sort_by(t[1..]));
    InsertByProps(t[0], sort_by(t[1..]));
  }
}
// </vc-helpers>

// <vc-spec>
method order_by_points(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> digits_sum(sorted[i]) <= digits_sum(sorted[j])
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  SortByProps(s);
  sorted := sort_by(s);
}
// </vc-code>

