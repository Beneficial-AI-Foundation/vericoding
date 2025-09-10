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
lemma count_occurrences_lemma(s: seq<int>, value: int)
  ensures count_occurrences(s, value) >= 0
{
}

lemma count_occurrences_non_empty(s: seq<int>, value: int)
  requires |s| > 0
  ensures count_occurrences(s, value) == count_occurrences(s[1..], value) + (if s[0] == value then 1 else 0)
{
}

lemma count_occurrences_upper_bound(s: seq<int>, value: int)
  ensures count_occurrences(s, value) <= |s|
{
}

lemma max_occurrence_exists(n: int, squares: seq<int>)
  requires n >= 1
  ensures exists col :: 1 <= col <= n && count_occurrences(squares, col) == max_occurrence(n, squares)
{
}

function max_occurrence(n: int, squares: seq<int>): int
  requires n >= 1
  reads squares
{
  max_occurrence_helper(n, squares, 1, 0)
}

function max_occurrence_helper(n: int, squares: seq<int>, current: int, max_so_far: int): int
  requires n >= 1
  requires 1 <= current <= n + 1
  requires max_so_far >= 0
  reads squares
  ensures 1 <= current <= n + 1 ==> max_so_far <= result <= max_so_far
  decreases n + 1 - current
{
  if current > n then
    max_so_far
  else
    max_occurrence_helper(n, squares, current + 1, 
                         if count_occurrences(squares, current) > max_so_far then 
                           count_occurrences(squares, current) 
                         else 
                           max_so_far)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, squares: seq<int>) returns (result: int)
    requires ValidInput(n, m, squares)
    ensures CorrectResult(n, squares, result)
// </vc-spec>
// <vc-code>
{
  result := 0;
  var current := 1;
  
  while current <= n
    invariant 1 <= current <= n + 1
    invariant result >= 0
    invariant forall col :: 1 <= col < current ==> result >= count_occurrences(squares, col)
    invariant exists col :: 1 <= col < current && result == count_occurrences(squares, col)
  {
    var count := count_occurrences(squares, current);
    if count > result {
      result := count;
    }
    current := current + 1;
  }
}
// </vc-code>

