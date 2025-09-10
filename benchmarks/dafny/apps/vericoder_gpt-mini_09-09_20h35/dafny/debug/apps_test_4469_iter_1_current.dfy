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
function SimulateQueries(queries: seq<(char, int)>, upto: int): BookshelfState
    requires 0 <= upto <= |queries|
    requires forall i :: 0 <= i < |queries| ==> queries[i].0 in {'L','R','?'}
    requires forall i :: 0 <= i < |queries| ==> queries[i].1 > 0
    requires forall i, j :: 0 <= i < j < |queries| && queries[i].0 in {'L','R'} && queries[j].0 in {'L','R'} ==> queries[i].1 != queries[j].1
    ensures forall k :: 0 <= k < upto && queries[k].0 in {'L','R'} ==> queries[k].1 in result.positions
    ensures forall id :: id in result.positions ==> result.head + 1 <= result.positions[id] <= result.tail
    decreases upto
{
  if upto == 0 then
    BookshelfState(map[], -1, -1)
  else
    let prev := SimulateQueries(queries, upto - 1) in
    let q := queries[upto - 1] in
    if q.0 == 'L' then
      let head := prev.head - 1 in
      let pos := head + 1 in
      let positions := prev.positions[q.1 := pos] in
      let tail := if prev.tail < pos then pos else prev.tail in
      BookshelfState(positions, head, tail)
    else if q.0 == 'R' then
      let tail := prev.tail + 1 in
      let pos := tail in
      let positions := prev.positions[q.1 := pos] in
      let head := if prev.head + 1 > pos then pos - 1 else prev.head in
      BookshelfState(positions, head, tail)
    else
      prev
}
// </vc-helpers>

// <vc-spec>
method solve(queries: seq<(char, int)>) returns (results: seq<int>)
    requires ValidInput(queries)
    ensures ValidOutput(queries, results)
// </vc-spec>
// <vc-code>
{
  var res := [];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|
    invariant |res| == |set j | 0 <= j < i && queries[j].0 == '?'|
    invariant forall r_idx :: 0 <= r_idx < |res| ==>
                (exists q_idx :: 0 <= q_idx < i && queries[q_idx].0 == '?' &&
                 res[r_idx] == ComputeMinRemovals(queries, q_idx))
    invariant forall q_idx :: 0 <= q_idx < i && queries[q_idx].0 == '?' ==>
                (exists r_idx :: 0 <= r_idx < |res| && res[r_idx] == ComputeMinRemovals(queries, q_idx))
  {
    if queries[i].0 == '?' {
      var r := ComputeMinRemovals(queries, i);
      res := res + [r];
    }
    i := i + 1;
  }
  results := res;
}
// </vc-code>

