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
// No additional helpers needed for this implementation
// </vc-helpers>

// <vc-spec>
method SolveBishops(positions: seq<(int, int)>) returns (result: int)
    requires ValidInput(positions)
    ensures ValidOutput(positions, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  var sumdiags: map<int, int> := map[];
  var diffdiags: map<int, int> := map[];
  
  for i := 0 to |positions|
  {
    var x := positions[i].0;
    var y := positions[i].1;
    var sumkey := x + y;
    var diffkey := x - y;
    
    var oldsum := if sumkey in sumdiags then sumdiags[sumkey] else 0;
    sumdiags := sumdiags[sumkey := oldsum + 1];
    
    var olddiff := if diffkey in diffdiags then diffdiags[diffkey] else 0;
    diffdiags := diffdiags[diffkey := olddiff + 1];
  }
  
  var result := 0;
  for key := min(sumdiags.Keys) to max(sumdiags.Keys)
  {
    if key in sumdiags
    {
      var c := sumdiags[key];
      result := result + (c * (c - 1)) / 2;
    }
  }
  
  for key := min(diffdiags.Keys) to max(diffdiags.Keys)
  {
    if key in diffdiags
    {
      var c := diffdiags[key];
      result := result + (c * (c - 1)) / 2;
    }
  }
}
// </vc-code>

