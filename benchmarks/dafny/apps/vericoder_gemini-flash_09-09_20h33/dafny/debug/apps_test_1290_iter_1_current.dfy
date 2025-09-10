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
function min_of_counts(n: int, squares: seq<int>): int
    requires n >= 1
    requires forall i :: 0 <= i < |squares| ==> 1 <= squares[i] <= n
    decreases n
{
    if n == 1 then
        count_occurrences(squares, 1)
    else
        var prev_min := min_of_counts(n - 1, squares);
        var current_count := count_occurrences(squares, n);
        min(prev_min, current_count)
}

function min(a: int, b: int): int {
    if a < b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, squares: seq<int>) returns (result: int)
    requires ValidInput(n, m, squares)
    ensures CorrectResult(n, squares, result)
// </vc-spec>
// <vc-code>
{
    var min_count := count_occurrences(squares, 1);
    var i := 2;
    while i <= n
        invariant 1 <= i <= n + 1
        invariant forall k :: 1 <= k < i ==> min_count <= count_occurrences(squares, k)
        invariant exists k :: 1 <= k < i && min_count == count_occurrences(squares, k)
    {
        min_count := min(min_count, count_occurrences(squares, i));
        i := i + 1;
    }
    return min_count;
}
// </vc-code>

