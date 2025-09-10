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
function CountPrefix(positions: seq<(int, int)>, k: int): int
    requires 0 <= k <= |positions|
{
    if k == 0 then 0 else CountAttackingPairs(positions[..k])
}

lemma CountPrefixFullEq(positions: seq<(int, int)>)
    requires ValidInput(positions)
    ensures CountPrefix(positions, |positions|) == CountAttackingPairs(positions)
{
    // If |positions| >= 1 (by ValidInput), CountPrefix(positions, |positions|) unfolds to CountAttackingPairs(positions[..|positions|])
    // and positions[..|positions|] == positions, hence equality holds.
}
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
    invariant res == CountPrefix(positions, i)
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
  // Relate prefix-count to the specified CountAttackingPairs for the full sequence
  if n >= 1 {
    CountPrefixFullEq(positions);
  }
  result := res;
}
// </vc-code>

