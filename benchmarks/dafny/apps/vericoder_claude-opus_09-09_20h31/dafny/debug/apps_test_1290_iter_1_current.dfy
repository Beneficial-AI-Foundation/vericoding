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
        assert count_occurrences(s, value) == 0;
    } else {
        count_occurrences_non_negative(s[1..], value);
    }
}

lemma count_occurrences_bound(s: seq<int>, value: int)
    ensures count_occurrences(s, value) <= |s|
{
    if |s| == 0 {
        assert count_occurrences(s, value) == 0;
    } else {
        count_occurrences_bound(s[1..], value);
        if s[0] == value {
            assert count_occurrences(s, value) == 1 + count_occurrences(s[1..], value);
        } else {
            assert count_occurrences(s, value) == count_occurrences(s[1..], value);
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
    var min_count := |squares| + 1;
    var col := 1;
    
    while col <= n
        invariant 1 <= col <= n + 1
        invariant min_count >= 0
        invariant forall c :: 1 <= c < col ==> min_count <= count_occurrences(squares, c)
        invariant col > 1 ==> exists c :: 1 <= c < col && min_count == count_occurrences(squares, c)
        invariant col == 1 ==> min_count == |squares| + 1
    {
        var current_count := 0;
        var i := 0;
        
        while i < |squares|
            invariant 0 <= i <= |squares|
            invariant current_count == count_occurrences(squares[..i], col)
            invariant current_count >= 0
        {
            if squares[i] == col {
                current_count := current_count + 1;
            }
            assert squares[..i+1] == squares[..i] + [squares[i]];
            i := i + 1;
        }
        
        assert squares[..|squares|] == squares;
        assert current_count == count_occurrences(squares, col);
        
        if current_count < min_count {
            min_count := current_count;
        }
        
        col := col + 1;
    }
    
    count_occurrences_non_negative(squares, 1);
    count_occurrences_bound(squares, 1);
    
    result := min_count;
}
// </vc-code>

