predicate ValidInput(queries: seq<(char, int)>)
{
    && |queries| > 0
    && (forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'})
    && (forall i :: 0 <= i < |queries| ==> queries[i].1 > 0)
    && (forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1)
    && (forall i :: 0 <= i < |queries| && queries[i].0 == '?' ==> 
        exists j :: 0 <= j < i && queries[j].0 in {'L', 'R'} && queries[j].1 == queries[i].1)
    && (exists i :: 0 <= i < |queries| && queries[i].0 == '?')
}

predicate ValidOutput(queries: seq<(char, int)>, results: seq<int>)
    requires ValidInput(queries)
{
    && |results| == |set i | 0 <= i < |queries| && queries[i].0 == '?'|
    && (forall i :: 0 <= i < |results| ==> results[i] >= 0)
    && (forall r_idx :: 0 <= r_idx < |results| ==> 
        (exists q_idx :: 0 <= q_idx < |queries| && queries[q_idx].0 == '?' &&
         results[r_idx] == ComputeMinRemovals(queries, q_idx)))
    && (forall q_idx :: 0 <= q_idx < |queries| && queries[q_idx].0 == '?' ==>
        (exists r_idx :: 0 <= r_idx < |results| &&
         results[r_idx] == ComputeMinRemovals(queries, q_idx)))
}

datatype BookshelfState = BookshelfState(positions: map<int, int>, head: int, tail: int)

function ComputeMinRemovals(queries: seq<(char, int)>, query_idx: int): int
    requires 0 <= query_idx < |queries|
    requires queries[query_idx].0 == '?'
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    requires forall i :: 0 <= i < |queries| && queries[i].0 == '?' ==> 
        exists j :: 0 <= j < i && queries[j].0 in {'L', 'R'} && queries[j].1 == queries[i].1
{
    var book_id := queries[query_idx].1;
    var state := SimulateQueries(queries, query_idx);
    assert book_id in state.positions;
    var pos := state.positions[book_id];
    var left_removals := pos - state.head;
    var right_removals := state.tail - pos;
    var min_removals := if left_removals <= right_removals then left_removals else right_removals;
    min_removals - 1
}

// <vc-helpers>
function SimulateQueries(queries: seq<(char, int)>, end_idx: int): BookshelfState
    requires 0 <= end_idx <= |queries|
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < end_idx && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    ensures result.head == -1 || result.head >= 0
    ensures result.tail == -1 || result.tail >= 0
    ensures result.head == -1 <==> result.tail == -1
    ensures result.head != -1 ==> result.head <= result.tail
{
    if end_idx == 0 then
        BookshelfState(map[], -1, -1)
    else
        var prev_state := SimulateQueries(queries, end_idx - 1);
        var op := queries[end_idx - 1].0;
        var book_id := queries[end_idx - 1].1;
        
        if op == 'L' || op == 'R' then
            if prev_state.head == -1 then
                BookshelfState(prev_state.positions[book_id := 0], 0, 0)
            else if op == 'L' then
                var new_head := prev_state.head - 1;
                var new_positions := prev_state.positions[book_id := new_head];
                BookshelfState(new_positions, new_head, prev_state.tail)
            else
                var new_tail := prev_state.tail + 1;
                var new_positions := prev_state.positions[book_id := new_tail];
                BookshelfState(new_positions, prev_state.head, new_tail)
        else
            prev_state
}

function count(queries: seq<(char, int)>, op: char): int
{
    if |queries| == 0 then 0
    else (if queries[0].0 == op then 1 else 0) + count(queries[1..], op)
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(char, int)>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidOutput(queries, results)
// </vc-spec>
// <vc-code>
{
    var question_indices := [];
    var i := 0;
    while i < |queries|
        invariant 0 <= i <= |queries|
        invariant forall j :: 0 <= j < |question_indices| ==> 0 <= question_indices[j] < i && queries[question_indices[j]].0 == '?'
        invariant |question_indices| == count(queries[..i], '?')
        invariant forall j, k :: 0 <= j < k < |question_indices| ==> question_indices[j] < question_indices[k]
    {
        if queries[i].0 == '?' {
            question_indices := question_indices + [i];
        }
        i := i + 1;
    }
    
    results := [];
    var idx := 0;
    while idx < |question_indices|
        invariant 0 <= idx <= |question_indices|
        invariant |results| == idx
        invariant forall j :: 0 <= j < idx ==> results[j] == ComputeMinRemovals(queries, question_indices[j])
    {
        var q_idx := question_indices[idx];
        var book_id := queries[q_idx].1;
        var state := SimulateQueries(queries, q_idx);
        assert book_id in state.positions;
        var pos := state.positions[book_id];
        var left_removals := pos - state.head;
        var right_removals := state.tail - pos;
        var min_removals := if left_removals <= right_removals then left_removals else right_removals;
        results := results + [min_removals - 1];
        idx := idx + 1;
    }
}
// </vc-code>

