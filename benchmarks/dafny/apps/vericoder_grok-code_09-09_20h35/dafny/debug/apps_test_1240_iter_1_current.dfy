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
// No additional helpers needed
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
  var original_L := sum_left(columns);
  var original_R := sum_right(columns);
  var original_diff := original_L - original_R;
  var original_beauty := abs(original_diff);
  var max_beauty := original_beauty;
  var best_i := -1;
  var i := 0;
  while i < |columns|
    invariant 0 <= i <= |columns|
    invariant -1 <= best_i < i
    invariant if best_i == -1 then max_beauty == original_beauty else best_i >= 0 && max_beauty > original_beauty
    invariant 0 <= original_beauty <= max_beauty
  {
    var a := columns[i].0;
    var b := columns[i].1;
    var delta := 2 * (b - a);
    var new_diff := original_diff + delta;
    var new_beauty := abs(new_diff);
    if new_beauty > max_beauty {
      max_beauty := new_beauty;
      best_i := i;
    }
    i := i + 1;
  }
  if best_i >= 0 {
    result := best_i + 1;
  } else {
    result := 0;
  }
}
// </vc-code>

