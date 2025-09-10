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
lemma CountRange(s: seq<int>, value: int)
  ensures 0 <= count_occurrences(s, value) <= |s|
  decreases |s|
{
  if |s| > 0 {
    CountRange(s[1..], value);
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
  var w := 1;
  var res := count_occurrences(squares, 1);
  CountRange(squares, 1);
  var i := 2;
  while i <= n
    invariant 2 <= i <= n + 1
    invariant 1 <= w <= n
    invariant res == count_occurrences(squares, w)
    invariant forall col :: 1 <= col < i ==> res <= count_occurrences(squares, col)
    invariant 0 <= res <= |squares|
    decreases n - i + 1
  {
    var c := count_occurrences(squares, i);
    CountRange(squares, i);
    if c < res {
      res := c;
      w := i;
    }
    i := i + 1;
  }
  result := res;
}
// </vc-code>

