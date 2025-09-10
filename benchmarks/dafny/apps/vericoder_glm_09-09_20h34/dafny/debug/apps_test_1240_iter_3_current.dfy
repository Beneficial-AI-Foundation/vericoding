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
// </vc-helpers>
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
    var D := sum_left(columns) - sum_right(columns);
    var orig_beauty := abs(D);
    var max_beauty := orig_beauty;
    var best_index := -1;

    for i := 0 to |columns|
        invariant 0 <= i <= |columns|
        invariant best_index == -1 || (0 <= best_index < i && max_beauty > orig_beauty)
        invariant forall j :: 0 <= j < i ==>
                     abs(D - 2 * (columns[j].0 - columns[j].1)) <= max_beauty
    {
        var delta := columns[i].0 - columns[i].1;
        var candidate := abs(D - 2 * delta);
        if candidate > max_beauty {
            max_beauty := candidate;
            best_index := i;
        }
    }

    result := if best_index == -1 then 0 else best_index+1;
}
// </vc-code>

