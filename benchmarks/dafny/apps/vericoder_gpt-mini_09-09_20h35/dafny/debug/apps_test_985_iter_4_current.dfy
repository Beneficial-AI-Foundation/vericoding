predicate ValidInput(positions: seq<(int, int)>)
{
    |positions| >= 1 && |positions| <= 200000 &&
    (forall i :: 0 <= i < |positions| ==> 
        1 <= positions[i].0 <= 1000 && 1 <= positions[i].1 <= 1000) &&
    (forall i, j :: 0 <= i < j < |positions| ==> positions[i] != positions[j])
}

function CountAttackingPairs(positions: seq<(int, int)>): int
    requires ValidInput(positions)
{
    |set i, j | 0 <= i < j < |positions| && 
               (positions[i].0 + positions[i].1 == positions[j].0 + positions[j].1 ||
                positions[i].0 - positions[i].1 == positions[j].0 - positions[j].1) :: (i, j)|
}

predicate ValidOutput(positions: seq<(int, int)>, result: int)
    requires ValidInput(positions)
{
    result == CountAttackingPairs(positions) && result >= 0
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SolveBishops(positions: seq<(int, int)>) returns (result: int)
    requires ValidInput(positions)
    ensures ValidOutput(positions, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var n := |positions|;
  var sumCount := new int[2001];
  var diffCount := new int[2001];
  var res := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant res == |set a, b | 0 <= a < b < i &&
                         (positions[a].0 + positions[a].1 == positions[b].0 + positions[b].1 ||
                          positions[a].0 - positions[a].1 == positions[b].0 - positions[b].1)
                      :: (a, b)|
    invariant forall idx :: 0 <= idx < 2001 ==>
                 sumCount[idx] == |set p | 0 <= p < i && positions[p].0 + positions[p].1 == idx|
    invariant forall idx :: 0 <= idx < 2001 ==>
                 diffCount[idx] == |set p | 0 <= p < i && positions[p].0 - positions[p].1 + 1000 == idx|
  {
    var p := positions[i];
    var s := p.0 + p.1;
    var d := p.0 - p.1 + 1000;
    var newPairs := sumCount[s] + diffCount[d];
    res := res + newPairs;
    sumCount[s] := sumCount[s] + 1;
    diffCount[d] := diffCount[d] + 1;
    i := i + 1;
  }
  assert res == |set a, b | 0 <= a < b < n &&
                       (positions[a].0 + positions[a].1 == positions[b].0 + positions[b].1 ||
                        positions[a].0 - positions[a].1 == positions[b].0 - positions[b].1)
                    :: (a, b)|;
  assert res == CountAttackingPairs(positions);
  result := res;
}
// </vc-code>

