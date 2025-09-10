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
lemma {:induction s} count_occurrences_correct(s : seq<int>, value : int)
    ensures count_occurrences(s, value) == |set i | 0 <= i < |s| && s[i] == value|
{
    if |s| == 0 {
    } else {
        count_occurrences_correct(s[1..], value);
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
    var min_freq := m + 1;
    var achieved : bool := false;
    var col := 1;
    while col <= n
        invariant 0 <= min_freq <= m + 1
        invariant forall c :: 1 <= c < col ==> min_freq <= count_occurrences(squares, c)
        invariant achieved <==> (exists c :: 1 <= c < col && count_occurrences(squares, c) == min_freq)
        decreases n - col + 1
    {
        var cnt := count_occurrences(squares, col);
        if cnt < min_freq {
            min_freq := cnt;
            achieved := true;
        } else if cnt == min_freq {
            achieved := true;
        }
        col := col + 1;
    }
    assert forall c :: 1 <= c <= n ==> min_freq <= count_occurrences(squares, c);
    assert exists c :: 1 <= c <= n && count_occurrences(squares, c) == min_freq;
    result := min_freq;
}
// </vc-code>

