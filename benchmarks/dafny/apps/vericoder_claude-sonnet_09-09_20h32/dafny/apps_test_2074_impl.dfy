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
lemma seq_indexing_lemma<T>(s: seq<T>, i: int)
    requires 0 <= i < |s|
    ensures s[i] in s
{
}

lemma seq_construction_lemma(grid: seq<seq<int>>, i: int)
    requires ValidGrid(grid)
    requires 0 <= i < |grid|
    ensures seq_min(grid[i]) in grid[i]
    ensures forall x :: x in grid[i] ==> seq_min(grid[i]) <= x
{
}

lemma row_mins_properties(grid: seq<seq<int>>)
    requires ValidGrid(grid)
    ensures var row_mins := seq(|grid|, i requires 0 <= i < |grid| => seq_min(grid[i]));
            |row_mins| == |grid|
    ensures var row_mins := seq(|grid|, i requires 0 <= i < |grid| => seq_min(grid[i]));
            forall j :: 0 <= j < |row_mins| ==> row_mins[j] == seq_min(grid[j])
{
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
    var row_mins := seq(|grid|, i requires 0 <= i < |grid| => seq_min(grid[i]));
    
    assert |row_mins| == |grid|;
    assert |grid| > 0;
    assert |row_mins| > 0;
    
    row_mins_properties(grid);
    
    result := seq_max(row_mins);
}
// </vc-code>

