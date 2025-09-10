predicate ValidInput(n: int, m: int, squares: seq<int>) {
    n >= 1 && n <= 1000 &&
    m >= 1 && m <= 1000 &&
    |squares| == m &&
    forall i :: 0 <= i < |squares| ==> 1 <= squares[i] <= n
}

function count_occurrences(s: seq<int>, value: int): int
{
    if |s| == 0 then 0
    else (if s[0] == value then 1 else 0) + count_occurrences(s[1..], value)
}

predicate CorrectResult(n: int, squares: seq<int>, result: int) {
    0 <= result <= |squares| &&
    (forall col :: 1 <= col <= n ==> result <= count_occurrences(squares, col)) &&
    (exists col :: 1 <= col <= n && result == count_occurrences(squares, col))
}

// <vc-helpers>
lemma CountNonNegative(s: seq<int>, v: int)
  ensures count_occurrences(s, v) >= 0
  decreases |s|
{
  if |s| == 0 {
    // base case: count_occurrences([], v) == 0
  } else {
    CountNonNegative(s[1..], v);
    // count_occurrences(s, v) == (if s[0] == v then 1 else 0) + count_occurrences(s[1..], v)
    // both summands are >= 0, so the whole sum is >= 0
  }
}

lemma CountAtMostLen(s: seq<int>, v: int)
  ensures count_occurrences(s, v) <= |s|
  decreases |s|
{
  if |s| == 0 {
    // base case: count_occurrences([], v) == 0 <= 0
  } else {
    CountAtMostLen(s[1..], v);
    // by induction count_occurrences(s[1..], v) <= |s[1..]| == |s|-1
    // (if s[0]==v then 1 else 0) <= 1, so sum <= 1 + (|s|-1) == |s|
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, squares: seq<int>) returns (result: int)
    requires ValidInput(n, m, squares)
    ensures CorrectResult(n, squares, result)
// </vc-spec>
// <vc-code>
{
  var r := m;
  var col := 1;
  while col <= n
    invariant 1 <= col <= n + 1
    invariant 0 <= r <= m
    invariant forall k :: 1 <= k < col ==> r <= count_occurrences(squares, k)
    invariant col == 1 || (exists k :: 1 <= k < col && r == count_occurrences(squares, k))
    decreases n - col + 1
  {
    var c := count_occurrences(squares, col);
    CountNonNegative(squares, col);
    CountAtMostLen(squares, col);
    if c < r {
      r := c;
    }
    col := col + 1;
  }
  result := r;
}
// </vc-code>

