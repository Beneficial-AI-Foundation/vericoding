predicate ValidInput(columns: seq<(int, int)>)
{
    forall i :: 0 <= i < |columns| ==> columns[i].0 > 0 && columns[i].1 > 0
}

function abs(x: int): int
{
    if x >= 0 then x else -x
}

function sum_left(columns: seq<(int, int)>): int
{
    if |columns| == 0 then 0
    else columns[0].0 + sum_left(columns[1..])
}

function sum_right(columns: seq<(int, int)>): int
{
    if |columns| == 0 then 0
    else columns[0].1 + sum_right(columns[1..])
}

// <vc-helpers>
lemma NewBeautyEqualsDiff(L:int, R:int, a:int, b:int)
    ensures abs((L - R) + 2*(b - a)) == abs((L - a + b) - (R - b + a))
{
    assert (L - R) + 2*(b - a) == (L - a + b) - (R - b + a);
    assert abs((L - R) + 2*(b - a)) == abs((L - a + b) - (R - b + a));
}
// </vc-helpers>

// <vc-spec>
method solve(columns: seq<(int, int)>) returns (result: int)
    requires ValidInput(columns)
    ensures 0 <= result <= |columns|
    ensures var L := sum_left(columns);
            var R := sum_right(columns);
            var original_beauty := abs(L - R);
            if result == 0 then
                forall i :: 0 <= i < |columns| ==> 
                    var new_L := L - columns[i].0 + columns[i].1;
                    var new_R := R - columns[i].1 + columns[i].0;
                    abs(new_L - new_R) <= original_beauty
            else
                1 <= result <= |columns| &&
                var best_idx := result - 1;
                var best_L := L - columns[best_idx].0 + columns[best_idx].1;
                var best_R := R - columns[best_idx].1 + columns[best_idx].0;
                var best_beauty := abs(best_L - best_R);
                best_beauty > original_beauty &&
                forall i :: 0 <= i < |columns| ==> 
                    var new_L := L - columns[i].0 + columns[i].1;
                    var new_R := R - columns[i].1 + columns[i].0;
                    abs(new_L - new_R) <= best_beauty
// </vc-spec>
// <vc-code>
{
  var n := |columns|;
  var L := sum_left(columns);
  var R := sum_right(columns);
  var diff := L - R;
  var original := abs(diff);

  var best := original;
  var bestIdx := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= bestIdx <= i
    invariant best >= original
    invariant (bestIdx == 0 ==> best == original)
    invariant (bestIdx > 0 ==> 0 <= bestIdx - 1 < i)
    invariant (bestIdx > 0 ==> best == abs(diff + 2*(columns[bestIdx - 1].1 - columns[bestIdx - 1].0)))
    invariant forall j :: 0 <= j < i ==> abs(diff + 2*(columns[j].1 - columns[j].0)) <= best
    decreases n - i
  {
    var cand := abs(diff + 2*(columns[i].1 - columns[i].0));
    if cand > best {
      best := cand;
      bestIdx := i + 1;
    }
    i := i + 1;
  }

  if bestIdx == 0 {
    result := 0;
    forall j | 0 <= j < n {
      assert j < i;
      assert abs(diff + 2*(columns[j].1 - columns[j].0)) <= best;
      assert best == original;
      assert abs(diff + 2*(columns[j].1 - columns[j].0)) <= original;
      NewBeautyEqualsDiff(L, R, columns[j].0, columns[j].1);
      assert abs((L - columns[j].0 + columns[j].1) - (R - columns[j].1 + columns[j].0)) ==
             abs(diff + 2*(columns[j].1 - columns[j].0));
      assert abs((L - columns[j].0 + columns[j].1) - (R - columns[j].1 + columns[j].0)) <= original;
    }
  } else {
    result := bestIdx;
    var idx := result - 1;
    assert 0 <= idx < n;
    assert best > original;
    assert best == abs(diff + 2*(columns[idx].1 - columns[idx].0));
    NewBeautyEqualsDiff(L, R, columns[idx].0, columns[idx].1);
    assert abs((L - columns[idx].0 + columns[idx].1) - (R - columns[idx].1 + columns[idx].0)) ==
           abs(diff + 2*(columns[idx].1 - columns[idx].0
// </vc-code>

