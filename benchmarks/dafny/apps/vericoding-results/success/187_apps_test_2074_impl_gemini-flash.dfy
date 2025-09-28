// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected array initialization for `seq<int>` in Dafny. Sequences are immutable, so instead of creating an array and assigning to it, we construct the sequence using a comprehension or concatenation. */
function GetRowMins(grid: seq<seq<int>>): seq<int>
    requires ValidGrid(grid)
    ensures |GetRowMins(grid)| == |grid|
    ensures forall i :: 0 <= i < |grid| ==> GetRowMins(grid)[i] == seq_min(grid[i])
{
    seq(|grid|, i requires 0 <= i < |grid| => seq_min(grid[i]))
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
/* code modified by LLM (iteration 5): Calls the `GetRowMins` helper function to compute the minimum value of each row and then finds the maximum among these row minimums. */
{
    var row_mins := GetRowMins(grid);
    result := seq_max(row_mins);
}
// </vc-code>
