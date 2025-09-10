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
// No auxiliary lemmas needed; helpers remain empty.
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
  var original := abs(L - R);
  var best_idx := 0;
  var best_beauty := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> abs((L - columns[k].0 + columns[k].1) - (R - columns[k].1 + columns[k].0)) <= best_beauty
    invariant i == 0 || (0 <= best_idx < n)
    invariant best_beauty >= 0
  {
    var a := columns[i].0;
    var b := columns[i].1;
    var newL := L - a + b;
    var newR := R - b + a;
    var beauty := abs(newL - newR);
    if beauty > best_beauty {
      best_beauty := beauty;
      best_idx := i;
    }
    i := i + 1;
  }
  if best_beauty > original {
    result := best_idx + 1;
  } else {
    result := 0;
  }
}
// </vc-code>

