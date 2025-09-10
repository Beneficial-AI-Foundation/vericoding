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
    requires ValidInput(positions)
    requires 0 <= k <= |positions|
{
    if k == 0 then 0 else CountAttackingPairs(positions[..k])
}

lemma ValidInputPrefix(positions: seq<(int,int)>, k: int)
    requires ValidInput(positions)
    requires 1 <= k <= |positions|
    ensures ValidInput(positions[..k])
{
    // length bounds
    assert |positions[..k]| == k;
    assert k >= 1;
    assert k <= 200000;

    // ranges for each element in prefix
    forall i | 0 <= i < k
        ensures 1 <= positions[..k][i].0 <= 1000 && 1 <= positions[..k][i].1 <= 1000
    {
        assert positions[..k][i] == positions[i];
        // from ValidInput(positions)
        assert 1 <= positions[i].0 <= 1000 && 1 <= positions[i].1 <= 1000;
    }

    // uniqueness in prefix
    forall i, j | 0 <= i < j < k
        ensures positions[..k][i] != positions[..k][j]
    {
        assert positions[..k][i] == positions[i];
        assert positions[..k][j] == positions[j];
        // from ValidInput(positions)
        assert positions[i] != positions[j];
    }
}

lemma CountAttackingPairsPrefixAdd(positions: seq<(int,int)>, k: int)
    requires ValidInput(positions)
    requires 0 <= k < |positions|
    ensures CountAttackingPairs(positions[..k+1]) ==
            CountAttackingPairs(positions[..k]) +
            |set i | 0 <= i < k && (positions[i].0 + positions[i].1 == positions[k].0 + positions[k].1 ||
                                     positions[i].0 - positions[i].1 == positions[k].0 - positions[k].1)|
{
    // Decompose pairs (i,j) with 0 <= i < j < k+1 into:
    // (A) those with j < k (i.e., counted by CountAttackingPairs(positions[..k]))
    // (B) those with j == k (i.e., i < k and attacking positions[i] with positions[k])
    calc {
        CountAttackingPairs(positions[..k+1]);
        == |set i,j | 0 <= i < j < k+1 &&
            (positions[i].0 + positions[i].1 == positions[j].0 + positions[j].1 ||
             positions[i].0 - positions[i].1 == positions[j].0 - positions[j].1) :: (i,j)|;
        == |set i,j | 0 <= i < j < k &&
            (positions[i].0 + positions[i].1 == positions[j].0 + positions[j].1 ||
             positions[i].0 - positions[i].1 == positions[j].0 - positions[j].1) :: (i,j)|
          + |set i | 0 <= i < k &&
            (positions[i].0 + positions[i].1 == positions[k].0 + positions[k].1 ||
             positions[i].0 - positions[i].1 == positions[k].0 - positions[k].1)|;
    }
    // The first summand is CountAttackingPairs(positions[..k])
    assert CountAttackingPairs(positions[..k]) ==
           |set i,j | 0 <= i < j < k &&
            (positions[i].0 + positions[i].1 == positions[j].0 + positions[j].1 ||
             positions[i].0 - positions[i].1 == positions[j].0 - positions[j].1) :: (i,j)|;
    // so the equality in the ensures clause holds
}

lemma CountPrefixFullEq(positions: seq<(int, int)>)
    requires ValidInput(positions)
    ensures CountPrefix(positions, |positions|) == CountAttackingPairs(positions)
{
    // CountPrefix(positions, |positions|) unfolds to CountAttackingPairs(positions[..|positions|])
    // and positions[..|positions|] == positions
    assert positions[..|positions|] == positions;
    // CountPrefix requires ValidInput(positions) so the function call is valid
    assert CountPrefix(positions, |positions|) == CountAttackingPairs(positions[..|positions|]);
    assert CountAttackingPairs(positions[..|positions|]) == CountAttackingPairs(positions);
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

    // Basic bounds for indices
    assert 0 <= s < 2001;
    assert 0 <= d < 2001;

    // Use the decomposition lemma to relate CountPrefix(., i+1) to CountPrefix(., i)
    CountAttackingPairsPrefixAdd(positions, i);

    // Prove that no previous index can satisfy both sum and diff equality simultaneously
    assert forall t | 0 <= t < i ::
      !(positions[t].0 + positions[t].1 == s && positions[t].0 - positions[t].1 == p.0 - p.1)
    {
      assume 0 <= t < i;
      if positions[t].0 + positions[t].1 == s && positions[t].
// </vc-code>

