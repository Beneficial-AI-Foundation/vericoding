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

lemma SortedTail(t: seq<int>)
  requires SortedByDigitSum(t)
  ensures SortedByDigitSum(t[1..])
{
  forall i, j | 0 <= i < j < |t[1..]| {
    assert 0 <= i + 1 < j + 1 < |t|;
    assert (t[1..])[i] == t[i+1];
    assert (t[1..])[j] == t[j+1];
    assert digits_sum(t[i+1]) <= digits_sum(t[j+1]);
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
      if jj == 0 {
        assert digits_sum(([b] + u)[i]) == digits_sum(b);
        assert digits_sum(([b
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

lemma SortedTail(t: seq<int>)
  requires SortedByDigitSum(t)
  ensures SortedByDigitSum(t[1..])
{
  forall i, j | 0 <= i < j < |t[1..]| {
    assert 0 <= i + 1 < j + 1 < |t|;
    assert (t[1..])[i] == t[i+1];
    assert (t[1..])[j] == t[j+1];
    assert digits_sum(t[i+1]) <= digits_sum(t[j+1]);
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
      if jj == 0 {
        assert digits_sum(([b] + u)[i]) == digits_sum(b);
        assert digits_sum(([b
// </vc-code>

