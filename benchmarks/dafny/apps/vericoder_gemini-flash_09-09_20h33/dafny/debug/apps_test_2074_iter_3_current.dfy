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
        invariant max_of_mins == (if i == 0 then -2147483648 else seq_max(seq_of_row_mins(grid, i)))
    {
        var current_row_min := seq_min(grid[i]);
        if current_row_min > max_of_mins {
            max_of_mins := current_row_min;
        }
        i := i + 1;
    }
    result := max_of_mins;
}
// </vc-code>

