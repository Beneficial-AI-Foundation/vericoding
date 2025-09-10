predicate ValidGrid(grid: seq<seq<int>>) {
    |grid| > 0 && forall i :: 0 <= i < |grid| ==> |grid[i]| > 0
}

function seq_min(s: seq<int>): int
    requires |s| > 0
    ensures seq_min(s) in s
    ensures forall x :: x in s ==> seq_min(s) <= x
    decreases |s|
{
    if |s| == 1 then s[0]
    else if s[0] <= seq_min(s[1..]) then 
        assert forall x :: x in s[1..] ==> seq_min(s[1..]) <= x;
        assert forall x :: x in s ==> (x == s[0] || x in s[1..]);
        assert forall x :: x in s ==> s[0] <= x;
        s[0]
    else 
        assert seq_min(s[1..]) < s[0];
        assert seq_min(s[1..]) in s[1..];
        assert forall x :: x in s[1..] ==> seq_min(s[1..]) <= x;
        assert forall x :: x in s ==> (x == s[0] || x in s[1..]);
        assert forall x :: x in s ==> seq_min(s[1..]) <= x;
        seq_min(s[1..])
}

function seq_max(s: seq<int>): int
    requires |s| > 0
    ensures seq_max(s) in s
    ensures forall x :: x in s ==> seq_max(s) >= x
    decreases |s|
{
    if |s| == 1 then s[0]
    else if s[0] >= seq_max(s[1..]) then 
        assert forall x :: x in s[1..] ==> seq_max(s[1..]) >= x;
        assert forall x :: x in s ==> (x == s[0] || x in s[1..]);
        assert forall x :: x in s ==> s[0] >= x;
        s[0]
    else 
        assert seq_max(s[1..]) > s[0];
        assert seq_max(s[1..]) in s[1..];
        assert forall x :: x in s[1..] ==> seq_max(s[1..]) >= x;
        assert forall x :: x in s ==> (x == s[0] || x in s[1..]);
        assert forall x :: x in s ==> seq_max(s[1..]) >= x;
        seq_max(s[1..])
}

// <vc-helpers>
function seq_min_row(grid: seq<seq<int>>, row: int): int
    requires ValidGrid(grid) && 0 <= row < |grid|
    ensures seq_min_row(grid, row) == seq_min(grid[row])
{
    seq_min(grid[row])
}

function seq_of_row_mins(grid: seq<seq<int>>, length: int): seq<int>
    requires ValidGrid(grid) && 0 <= length <= |grid|
    ensures |seq_of_row_mins(grid, length)| == length
    ensures forall k :: 0 <= k < length ==> seq_of_row_mins(grid, length)[k] == seq_min(grid[k])
{
    seq(length, k requires 0 <= k < length => seq_min(grid[k]))
}

predicate IsMaxOfFirstIMins(max_val: int, grid: seq<seq<int>>, i: int)
    requires ValidGrid(grid) && 0 <= i <= |grid|
{
    if i == 0 then
        max_val == -2147483648
    else
        max_val == seq_max(seq_of_row_mins(grid, i))
}

lemma lemma_seq_max_append(s: seq<int>, x: int)
    requires |s| > 0
    ensures seq_max(s + [x]) == max(seq_max(s), x)
{
    if x >= seq_max(s) {
        assert forall y :: y in s ==> y <= seq_max(s) <= x;
        assert forall y :: y in s + [x] ==> y <= x;
        assert seq_max(s + [x]) == x;
    } else {
        assert forall y :: y in s ==> y <= seq_max(s);
        assert forall y :: y in s + [x] && y != x ==> y <= seq_max(s);
        assert seq_max(s + [x]) == seq_max(s);
    }
}

function max(a: int, b: int): int {
    if a >= b then a else b
}
// </vc-helpers>

// <vc-spec>
method solve(grid: seq<seq<int>>) returns (result: int)
    requires ValidGrid(grid)
    ensures (
        var row_mins := seq(|grid|, i requires 0 <= i < |grid| => seq_min(grid[i]));
        result == seq_max(row_mins)
    )
// </vc-spec>
// <vc-code>
{
    var max_of_mins := -2147483648; // Represents negative infinity for int

    var i := 0;
    while i < |grid|
        invariant 0 <= i <= |grid|
        invariant forall j :: 0 <= j < i ==> max_of_mins >= seq_min(grid[j])
        invariant IsMaxOfFirstIMins(max_of_mins, grid, i)
    {
        var current_row_min := seq_min(grid[i]);
        var old_max_of_mins := max_of_mins;
        if current_row_min > max_of_mins {
            max_of_mins := current_row_min;
        }

        assert IsMaxOfFirstIMins(max_of_mins, grid, i+1) by {
            if i == 0 {
                assert max_of_mins == current_row_min;
                assert seq_of_row_mins(grid, 1)[0] == seq_min(grid[0]);
                assert seq_max(seq_of_row_mins(grid, 1)) == seq_min(grid[0]);
            } else {
                var previous_row_mins := seq_of_row_mins(grid, i);
                var current_row_mins := seq_of_row_mins(grid, i+1);
                assert current_row_mins == previous_row_mins + [current_row_min];
                
                lemma_seq_max_append(previous_row_mins, current_row_min);
                assert seq_max(current_row_mins) == max(seq_max(previous_row_mins), current_row_min);
                assert max_of_mins == max(old_max_of_mins, current_row_min);
            }
        }
        i := i + 1;
    }
    result := max_of_mins;
}
// </vc-code>

