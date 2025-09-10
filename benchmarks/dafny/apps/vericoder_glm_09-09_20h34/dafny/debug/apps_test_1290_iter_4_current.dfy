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
lemma CountOccurrencesAppend(s: seq<int>, x: int, c: int)
    ensures count_occurrences(s + [x], c) == count_occurrences(s, c) + (if x == c then 1 else 0)
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert count_occurrences([x], c) == (if x == c then 1 else 0);
        assert count_occurrences(s, c) == 0;
    } else {
        calc {
            count_occurrences(s + [x], c);
            (if s[0] == c then 1 else 0) + count_occurrences(s[1..] + [x], c);
            { CountOccurrencesAppend(s[1..], x, c); }
            (if s[0] == c then 1 else 0) + (count_occurrences(s[1..], c) + (if x == c then 1 else 0));
            (if s[0] == c then 1 else 0) + count_occurrences(s[1..], c) + (if x == c then 1 else 0);
            count_occurrences(s, c) + (if x == c then 1 else 0);
        }
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
    var counts := new int[n+1];
    var j := 0;
    while j < m 
        invariant 0 <= j <= m
        invariant forall c :: 1 <= c <= n ==> counts[c] == count_occurrences(squares[0..j], c)
    {
        counts[squares[j]] := counts[squares[j]] + 1;
        j := j + 1;
    }

    var minSoFar := counts[1];
    var minColor := 1;
    var i := 2;
    while i <= n 
        invariant 2 <= i <= n+1
        invariant forall c :: 1 <= c < i ==> minSoFar <= counts[c]
        invariant 1 <= minColor < i
        invariant minSoFar == counts[minColor]
    {
        if counts[i] < minSoFar {
            minSoFar := counts[i];
            minColor := i;
        }
        i := i + 1;
    }
    result := minSoFar;
}
// </vc-code>

