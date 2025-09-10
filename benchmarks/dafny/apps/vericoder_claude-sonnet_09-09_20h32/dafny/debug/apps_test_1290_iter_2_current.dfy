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
lemma count_occurrences_non_negative(s: seq<int>, value: int)
    ensures count_occurrences(s, value) >= 0
{
    if |s| == 0 {
    } else {
        count_occurrences_non_negative(s[1..], value);
    }
}

lemma count_occurrences_bounded(s: seq<int>, value: int)
    ensures count_occurrences(s, value) <= |s|
{
    if |s| == 0 {
    } else {
        count_occurrences_bounded(s[1..], value);
    }
}

lemma count_occurrences_preservation(s: seq<int>, value: int, i: int)
    requires 0 <= i < |s|
    ensures count_occurrences(s, value) >= (if s[i] == value then 1 else 0)
{
    if |s| == 0 {
    } else if i == 0 {
    } else {
        count_occurrences_preservation(s[1..], value, i-1);
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
    var min_count := m + 1;
    var col := 1;
    
    while col <= n
        invariant 1 <= col <= n + 1
        invariant min_count >= 0
        invariant min_count <= m
        invariant col > 1 ==> (forall c :: 1 <= c < col ==> min_count <= count_occurrences(squares, c))
        invariant col > 1 ==> (exists c :: 1 <= c < col && min_count == count_occurrences(squares, c))
        invariant col == 1 ==> min_count == m + 1
    {
        count_occurrences_non_negative(squares, col);
        count_occurrences_bounded(squares, col);
        
        var count := count_occurrences(squares, col);
        
        if col == 1 || count < min_count {
            min_count := count;
        }
        
        col := col + 1;
    }
    
    result := min_count;
}
// </vc-code>

