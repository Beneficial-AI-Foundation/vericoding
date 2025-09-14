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
function SimulateQueries(queries: seq<(char, int)>, up_to: int): BookshelfState
    requires 0 <= up_to < |queries|
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    requires forall i :: 0 <= i < |queries| && queries[i].0 == '?' ==> 
        exists j :: 0 <= j < i && queries[j].0 in {'L', 'R'} && queries[j].1 == queries[i].1
    decreases up_to
{
    if up_to == 0 then
        if queries[0].0 == 'L' then
            BookshelfState(map[queries[0].1 := 0], 0, 0)
        else if queries[0].0 == 'R' then
            BookshelfState(map[queries[0].1 := 0], 0, 0)
        else
            BookshelfState(map[], 0, 0)
    else
        var prev_state := SimulateQueries(queries, up_to - 1);
        if queries[up_to].0 == 'L' then
            BookshelfState(
                prev_state.positions[queries[up_to].1 := prev_state.head - 1],
                prev_state.head - 1,
                prev_state.tail
            )
        else if queries[up_to].0 == 'R' then
            BookshelfState(
                prev_state.positions[queries[up_to].1 := prev_state.tail + 1],
                prev_state.head,
                prev_state.tail + 1
            )
        else
            prev_state
}

lemma SimulateQueriesPreservesBooks(queries: seq<(char, int)>, up_to: int, book_id: int)
    requires 0 <= up_to < |queries|
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L', 'R', '?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L', 'R'} && queries[j].0 in {'L', 'R'} ==> queries[i].1 != queries[j].1
    requires forall i :: 0 <= i < |queries| && queries[i].0 == '?' ==> 
        exists j :: 0 <= j < i && queries[j].0 in {'L', 'R'} && queries[j].1 == queries[i].1
    requires exists j :: 0 <= j <= up_to && queries[j].0 in {'L', 'R'} && queries[j].1 == book_id
    ensures book_id in SimulateQueries(queries, up_to).positions
    decreases up_to
{
    if up_to == 0 {
        if queries[0].0 in {'L', 'R'} && queries[0].1 == book_id {
        }
    } else {
        if queries[up_to].0 == 'L' {
            if queries[up_to].1 == book_id {
            } else {
                assert exists j :: 0 <= j < up_to && queries[j].0 in {'L', 'R'} && queries[j].1 == book_id;
                SimulateQueriesPreservesBooks(queries, up_to - 1, book_id);
            }
        } else if queries[up_to].0 == 'R' {
            if queries[up_to].1 == book_id {
            } else {
                assert exists j :: 0 <= j < up_to && queries[j].0 in {'L', 'R'} && queries[j].1 == book_id;
                SimulateQueriesPreservesBooks(queries, up_to - 1, book_id);
            }
        } else {
            assert exists j :: 0 <= j < up_to && queries[j].0 in {'L', 'R'} && queries[j].1 == book_id;
            SimulateQueriesPreservesBooks(queries, up_to - 1, book_id);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(char, int)>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidOutput(queries, results)
// </vc-spec>
// <vc-code>
{
    results := [];
    var positions: map<int, int> := map[];
    var head := 0;
    var tail := 0;
    
    var i := 0;
    while i < |queries|
        invariant 0 <= i <= |queries|
        invariant |results| == |set j | 0 <= j < i && queries[j].0 == '?'|
        invariant forall r_idx :: 0 <= r_idx < |results| ==> results[r_idx] >= 0
        invariant forall r_idx :: 0 <= r_idx < |results| ==> 
            exists q_idx :: 0 <= q_idx < i && queries[q_idx].0 == '?' &&
             results[r_idx] == ComputeMinRemovals(queries, q_idx)
        invariant forall q_idx :: 0 <= q_idx < i && queries[q_idx].0 == '?' ==>
            exists r_idx :: 0 <= r_idx < |results| &&
             results[r_idx] == ComputeMinRemovals(queries, q_idx)
        invariant i > 0 ==> BookshelfState(positions, head, tail) == SimulateQueries(queries, i - 1)
        invariant i == 0 ==> positions == map[] && head == 0 && tail == 0
    {
        if queries[i].0 == 'L' {
            if i == 0 {
                positions := positions[queries[i].1 := 0];
            } else {
                head := head - 1;
                positions := positions[queries[i].1 := head];
            }
        } else if queries[i].0 == 'R' {
            if i == 0 {
                positions := positions[queries[i].1 := 0];
            } else {
                tail := tail + 1;
                positions := positions[queries[i].1 := tail];
            }
        } else {
            assert queries[i].0 == '?';
            var book_id := queries[i].1;
            if i > 0 {
                assert exists j :: 0 <= j < i && queries[j].0 in {'L', 'R'} && queries[j].1 == book_id;
                SimulateQueriesPreservesBooks(queries, i - 1, book_id);
            }
            assert book_id in positions;
            var pos := positions[book_id];
            var left_removals := pos - head;
            var right_removals := tail - pos;
            var min_removals := if left_removals <= right_removals then left_removals else right_removals;
            results := results + [min_removals - 1];
        }
        i := i + 1;
    }
}
// </vc-code>

