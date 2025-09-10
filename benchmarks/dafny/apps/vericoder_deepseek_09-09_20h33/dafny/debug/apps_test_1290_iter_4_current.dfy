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

lemma max_occurrence_exists(squares: seq<int>, n: int)
  requires n >= 1
  ensures exists col :: 1 <= col <= n && count_occurrences(squares, col) == max_occurrence(squares, n)
{
  if n == 1 {
    // Base case: only column 1 exists
  } else {
    max_occurrence_exists(squares, n - 1);
    // The maximum exists either at n or in the previous range
  }
}

function max_occurrence(squares: seq<int>, n: int): int
  requires n >= 1
{
  if n == 1 then
    count_occurrences(squares, 1)
  else
    var max_prev := max_occurrence(squares, n - 1);
    var curr_count := count_occurrences(squares, n);
    if curr_count > max_prev then curr_count else max_prev
}

lemma max_occurrence_monotonic(squares: seq<int>, n: int)
  requires n >= 1
  ensures forall k :: 1 <= k <= n ==> max_occurrence(squares, k) <= max_occurrence(squares, n)
{
  if n > 1 {
    max_occurrence_monotonic(squares, n - 1);
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
  result := 0;
  var current := 1;
  var witness_col := 1;
  
  // Handle the case when n == 1 separately to ensure proper initialization
  if n == 1 {
    result := count_occurrences(squares, 1);
    return;
  }
  
  while current <= n
    invariant 1 <= current <= n + 1
    invariant result >= 0
    invariant forall col :: 1 <= col < current ==> result >= count_occurrences(squares, col)
    invariant 1 <= witness_col < current || (current == 1 && witness_col == 1)
    invariant witness_col >= 1
    invariant current > 1 ==> result == count_occurrences(squares, witness_col)
  {
    var count := count_occurrences(squares, current);
    if count > result {
      result := count;
      witness_col := current;
    }
    current := current + 1;
  }
  
  // Postcondition verification
  max_occurrence_exists(squares, n);
}
// </vc-code>

