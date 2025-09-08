Two players play a sequential game on a grid of restaurant costs.
Emma (first player) chooses a row to maximize final cost.
Jack (second player) then chooses a column to minimize final cost.
Both play optimally. Find the resulting cost when both play optimally.

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

method solve(grid: seq<seq<int>>) returns (result: int)
    requires ValidGrid(grid)
    ensures (
        var row_mins := seq(|grid|, i requires 0 <= i < |grid| => seq_min(grid[i]));
        result == seq_max(row_mins)
    )
{
    var row_mins := [];
    for i := 0 to |grid|
        invariant |row_mins| == i
        invariant forall k :: 0 <= k < i ==> row_mins[k] == seq_min(grid[k])
    {
        var min_val := grid[i][0];
        for j := 1 to |grid[i]|
            invariant forall k :: 0 <= k < j ==> min_val <= grid[i][k]
            invariant exists k :: 0 <= k < j && min_val == grid[i][k]
            invariant min_val in grid[i][0..j]
        {
            if grid[i][j] < min_val {
                min_val := grid[i][j];
            }
        }
        assert forall k :: 0 <= k < |grid[i]| ==> min_val <= grid[i][k];
        assert min_val in grid[i];
        assert min_val == seq_min(grid[i]);
        row_mins := row_mins + [min_val];
    }

    assert row_mins == seq(|grid|, i requires 0 <= i < |grid| => seq_min(grid[i]));

    var max_val := row_mins[0];
    for i := 1 to |row_mins|
        invariant forall k :: 0 <= k < i ==> max_val >= row_mins[k]
        invariant exists k :: 0 <= k < i && max_val == row_mins[k]
        invariant max_val in row_mins[0..i]
    {
        if row_mins[i] > max_val {
            max_val := row_mins[i];
        }
    }

    assert forall k :: 0 <= k < |row_mins| ==> max_val >= row_mins[k];
    assert max_val in row_mins;
    assert max_val == seq_max(row_mins);
    return max_val;
}
