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
  } else {
    CountNonNegative(s[1..], v);
  }
}

lemma CountAtMostLen(s: seq<int>, v: int)
  ensures count_occurrences(s, v) <= |s|
  decreases |s|
{
  if |s| == 0 {
  } else {
    CountAtMostLen(s[1..], v);
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
  var r := count_occurrences(squares, 1);
  var col := 2;
  // establish invariants at loop entry
  CountNonNegative(squares, 1);
  CountAtMostLen(squares, 1);
  assert 0 <= r <= m;
  assert forall k :: 1 <= k < col ==> r <= count_occurrences(squares, k);
  assert exists k :: 1 <= k < col && r == count_occurrences(squares, k);

  while col <= n
    invariant 1 <= col <= n + 1
    invariant 0 <= r <= m
    invariant forall k :: 1 <= k < col ==> r <= count_occurrences(squares, k)
    invariant exists k :: 1 <= k < col && r == count_occurrences(squares, k)
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

