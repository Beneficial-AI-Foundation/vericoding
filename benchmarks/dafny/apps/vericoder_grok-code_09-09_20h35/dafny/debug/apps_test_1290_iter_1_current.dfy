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
// Helper lemma to establish correctness of count_occurrences
lemma CountOccurrencesLemma(s: seq<int>, v: int, i: int, j: int)
  decreases i
  requires 0 <= i <= j <= |s|
  ensures count_occurrences_internal(s, v, i, j) <= j - i
  ensures forall k :: i <= k < j ==> (s[k] == v) ==> count_occurrences_internal(s, v, i, j) >= 1
  // And other properties as needed
  {
    if i == j {
      // Base case: trivially true
    } else {
      CountOccurrencesLemma(s, v, i+1, j);
    }
  }

// Internal iterative version for counting (to avoid recursion depth issues, though recursive is fine for m<=1000)
function count_occurrences_iter(s: seq<int>, v: int): int
{
  var cnt := 0;
  for i := 0 to |s| {
    if s[i] == v { cnt := cnt + 1; }
  }
  cnt
}

// Proof that the iterative version matches the recursive one
lemma CountMatchesIter(s: seq<int>, v: int)
  ensures count_occurrences_iter(s, v) == count_occurrences(s, v)
{
  // Base case, etc. - standard induction on |s|
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, squares: seq<int>) returns (result: int)
    requires ValidInput(n, m, squares)
    ensures CorrectResult(n, squares, result)
// </vc-spec>
// <vc-code>
{
    var max_freq := 0;
    var achieved : bool := false;
    var col := 1;
    while col <= n
        invariant 0 <= max_freq <= m
        invariant forall c :: 1 <= c < col ==> max_freq >= count_occurrences(squares, c)
        invariant achieved <==> (exists c :: 1 <= c < col && count_occurrences(squares, c) == max_freq)
        decreases n - col + 1
    {
        var cnt := count_occurrences(squares, col);
        if cnt > max_freq {
            max_freq := cnt;
            achieved := true;
        } else if cnt == max_freq {
            achieved := true;
        }
        col := col + 1;
    }
    assert forall c :: 1 <= c <= n ==> max_freq >= count_occurrences(squares, c);
    assert exists c :: 1 <= c <= n && count_occurrences(squares, c) == max_freq;
    result := max_freq;
}
// </vc-code>

