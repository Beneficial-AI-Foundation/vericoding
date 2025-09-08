Given n columns and m squares appearing in specified columns, calculate points earned.
Each square stacks in its column. When all columns have at least one square,
the bottom row is removed (earning 1 point) and squares drop down.
Return total points earned.

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

lemma count_occurrences_extend_lemma(s: seq<int>, x: int, value: int)
    ensures count_occurrences(s + [x], value) == count_occurrences(s, value) + (if x == value then 1 else 0)
{
    if |s| == 0 {
        assert s + [x] == [x];
        assert count_occurrences([x], value) == (if x == value then 1 else 0);
        assert count_occurrences(s, value) == 0;
    } else {
        assert s + [x] == [s[0]] + (s[1..] + [x]);
        count_occurrences_extend_lemma(s[1..], x, value);
    }
}

method solve(n: int, m: int, squares: seq<int>) returns (result: int)
    requires ValidInput(n, m, squares)
    ensures CorrectResult(n, squares, result)
{
    var res := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall j :: 0 <= j < i ==> res[j] == 0
    {
        res[i] := 0;
        i := i + 1;
    }

    i := 0;
    while i < m
        invariant 0 <= i <= m
        invariant forall j :: 0 <= j < n ==> res[j] == count_occurrences(squares[..i], j + 1)
        invariant forall j :: 0 <= j < n ==> 0 <= res[j] <= i
    {
        var col := squares[i] - 1; // convert to 0-indexed
        assert 0 <= col < n;

        // Help Dafny understand the count_occurrences properties for all indices
        forall j | 0 <= j < n {
            count_occurrences_extend_lemma(squares[..i], squares[i], j + 1);
        }
        assert squares[..i+1] == squares[..i] + [squares[i]];
        assert squares[i] == col + 1;

        res[col] := res[col] + 1;
        i := i + 1;
    }

    assert squares[..m] == squares;
    assert forall j :: 0 <= j < n ==> res[j] == count_occurrences(squares, j + 1);
    assert forall j :: 0 <= j < n ==> 0 <= res[j] <= m;

    var minVal := res[0];
    var minIdx := 0;
    i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant 0 <= minIdx < n
        invariant minVal == res[minIdx]
        invariant forall j :: 0 <= j < i ==> minVal <= res[j]
        invariant 0 <= minVal <= m
    {
        if res[i] < minVal {
            minVal := res[i];
            minIdx := i;
        }
        i := i + 1;
    }

    assert forall j :: 0 <= j < n ==> minVal <= res[j];
    assert minVal == res[minIdx];
    assert 0 <= minIdx < n;
    assert minVal == count_occurrences(squares, minIdx + 1);
    assert 1 <= minIdx + 1 <= n;

    // Help prove the postcondition
    forall col | 1 <= col <= n 
        ensures minVal <= count_occurrences(squares, col)
    {
        assert count_occurrences(squares, col) == res[col - 1];
        assert minVal <= res[col - 1];
    }

    result := minVal;
}
