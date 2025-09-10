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

lemma count_occurrences_append(s: seq<int>, value: int, x: int)
    ensures count_occurrences(s + [x], value) == count_occurrences(s, value) + (if x == value then 1 else 0)
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert count_occurrences([x], value) == (if x == value then 1 else 0);
    } else {
        assert (s + [x])[0] == s[0];
        assert (s + [x])[1..] == s[1..] + [x];
        count_occurrences_append(s[1..], value, x);
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
    // First, compute the count for column 1
    var current_count := 0;
    var i := 0;
    
    while i < |squares|
        invariant 0 <= i <= |squares|
        invariant current_count == count_occurrences(squares[..i], 1)
        invariant current_count >= 0
    {
        var old_count := current_count;
        if squares[i] == 1 {
            current_count := current_count + 1;
        }
        assert squares[..i+1] == squares[..i] + [squares[i]];
        count_occurrences_append(squares[..i], 1, squares[i]);
        assert count_occurrences(squares[..i+1], 1) == count_occurrences(squares[..i], 1) + (if squares[i] == 1 then 1 else 0);
        assert current_count == old_count + (if squares[i] == 1 then 1 else 0);
        i := i + 1;
    }
    
    assert squares[..|squares|] == squares;
    assert current_count == count_occurrences(squares, 1);
    count_occurrences_bound(squares, 1);
    
    var min_count := current_count;
    var col := 2;
    
    while col <= n
        invariant 2 <= col <= n + 1
        invariant min_count >= 0
        invariant min_count <= |squares|
        invariant forall c :: 1 <= c < col ==> min_count <= count_occurrences(squares, c)
        invariant exists c :: 1 <= c < col && min_count == count_occurrences(squares, c)
    {
        current_count := 0;
        i := 0;
        
        while i < |squares|
            invariant 0 <= i <= |squares|
            invariant current_count == count_occurrences(squares[..i], col)
            invariant current_count >= 0
        {
            var old_count := current_count;
            if squares[i] == col {
                current_count := current_count + 1;
            }
            assert squares[..i+1] == squares[..i] + [squares[i]];
            count_occurrences_append(squares[..i], col, squares[i]);
            assert count_occurrences(squares[..i+1], col) == count_occurrences(squares[..i], col) + (if squares[i] == col then 1 else 0);
            assert current_count == old_count + (if squares[i] == col then 1 else 0);
            i := i + 1;
        }
        
        assert squares[..|squares|] == squares;
        assert current_count == count_occurrences(squares, col);
        count_occurrences_bound(squares, col);
        assert current_count <= |squares|;
        
        if current_count < min_count {
            min_count := current_count;
        }
        
        col := col + 1;
    }
    
    assert col == n + 1;
    assert forall c :: 1 <= c <= n ==> min_count <= count_occurrences(squares, c);
    assert exists c :: 1 <= c <= n && min_count == count_occurrences(squares, c);
    
    result := min_count;
}
// </vc-code>

