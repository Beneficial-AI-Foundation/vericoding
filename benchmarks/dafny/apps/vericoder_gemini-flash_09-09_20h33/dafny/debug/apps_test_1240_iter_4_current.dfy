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
function calculate_beauty_after_swap(L: int, R: int, col: (int, int)): int
{
    var new_L := L - col.0 + col.1;
    var new_R := R - col.1 + col.0;
    abs(new_L - new_R)
}

predicate IsMaxBeauty(columns: seq<(int, int)>, L: int, R: int, original_beauty: int, best_index: int, max_beauty_increase: int)
{
    if best_index == -1 then
        max_beauty_increase == 0 &&
        (forall i :: 0 <= i < |columns| ==> calculate_beauty_after_swap(L, R, columns[i]) - original_beauty <= 0)
    else
        0 <= best_index < |columns| &&
        max_beauty_increase == calculate_beauty_after_swap(L, R, columns[best_index]) - original_beauty &&
        max_beauty_increase > 0 &&
        (forall i :: 0 <= i < |columns| ==> calculate_beauty_after_swap(L, R, columns[i]) - original_beauty <= max_beauty_increase)
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
    var L := sum_left(columns);
    var R := sum_right(columns);
    var original_beauty := abs(L - R);

    var max_beauty_increase := 0;
    var best_index := -1;

    for i := 0 to |columns| - 1
        invariant 0 <= i <= |columns|
        invariant (best_index == -1 ==> max_beauty_increase == 0)
        invariant (best_index != -1 ==> 0 <= best_index < i &&
                                          calculate_beauty_after_swap(L, R, columns[best_index]) - original_beauty == max_beauty_increase &&
                                          max_beauty_increase > 0)
        invariant forall j :: 0 <= j < i ==> calculate_beauty_after_swap(L, R, columns[j]) - original_beauty <= max_beauty_increase
    {
        var current_beauty := calculate_beauty_after_swap(L, R, columns[i]);
        var beauty_increase := current_beauty - original_beauty;

        if beauty_increase > max_beauty_increase {
            max_beauty_increase := beauty_increase;
            best_index := i;
        }
    }
    
    // Prove the postcondition based on the loop invariants
    if best_index == -1 {
        result := 0;
        assert forall i :: 0 <= i < |columns| ==> calculate_beauty_after_swap(L, R, columns[i]) <= original_beauty;
    } else {
        result := best_index + 1;
        assert (calculate_beauty_after_swap(L, R, columns[best_index]) > original_beauty);
        assert forall i :: 0 <= i < |columns| ==> calculate_beauty_after_swap(L, R, columns[i]) <= calculate_beauty_after_swap(L, R, columns[best_index]);
    }
}
// </vc-code>

