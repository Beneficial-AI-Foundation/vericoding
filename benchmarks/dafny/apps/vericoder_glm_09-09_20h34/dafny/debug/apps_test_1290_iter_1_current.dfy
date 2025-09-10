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

// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, squares: seq<int>) returns (result: int)
    requires ValidInput(n, m, squares)
    ensures CorrectResult(n, squares, result)
// </vc-spec>
// <vc-code>
{
    var counts := new int[n+1];
    // Build the counts array: counts[i] for i in 1..n will be the count of i in squares.
    var j := 0;
    while j < m 
        invariant 0 <= j <= m
        invariant forall c :: 1 <= c <= n ==> counts[c] == count_occurrences(squares[0..j], c)
    {
        counts[squares[j]] := counts[squares[j]] + 1;
        j := j + 1;
    }

    // Now find the minimum count among columns 1 to n.
    var minSoFar := counts[1];
    var i := 2;
    while i <= n 
        invariant 2 <= i <= n+1
        invariant forall c :: 1 <= c <= i-1 ==> minSoFar <= counts[c]
        invariant exists c :: 1 <= c <= i-1 && minSoFar == counts[c]
    {
        if counts[i] < minSoFar {
            minSoFar := counts[i];
        }
        i := i + 1;
    }
    result := minSoFar;
}
// </vc-code>

