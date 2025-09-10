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
lemma lemma_diff_sign(i: int, columns: seq<(int, int)>, L: int, R: int)
    requires ValidInput(columns)
    requires 0 <= i < |columns|
    ensures var new_L := L - columns[i].0 + columns[i].1;
            var new_R := R - columns[i].1 + columns[i].0;
            abs(new_L - new_R) == abs((L - R) - 2*(columns[i].0 - columns[i].1))
{
}

lemma lemma_compare_beauty(i: int, j: int, columns: seq<(int, int)>, L: int, R: int)
    requires ValidInput(columns)
    requires 0 <= i < |columns|
    requires 0 <= j < |columns|
    ensures var new_L_i := L - columns[i].0 + columns[i].1;
            var new_R_i := R - columns[i].1 + columns[i].0;
            var new_L_j := L - columns[j].0 + columns[j].1;
            var new_R_j := R - columns[j].1 + columns[j].0;
            abs(new_L_i - new_R_i) <= abs(new_L_j - new_R_j) || abs(new_L_j - new_R_j) <= abs(new_L_i - new_R_i)
{
}

lemma lemma_beauty_monotonic(i: int, columns: seq<(int, int)>, L: int, R: int, best_beauty: int)
    requires ValidInput(columns)
    requires 0 <= i < |columns|
    requires best_beauty >= abs(L - R)
    ensures var new_L := L - columns[i].0 + columns[i].1;
            var new_R := R - columns[i].1 + columns[i].0;
            abs(new_L - new_R) <= best_beauty || best_beauty < abs(new_L - new_R)
{
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
    
    var best_idx := 0;
    var best_beauty := original_beauty;
    var found := false;
    
    var i := 0;
    while i < |columns|
        invariant 0 <= i <= |columns|
        invariant 0 <= best_idx < |columns| || (best_idx == 0 && |columns| == 0)
        invariant best_beauty >= original_beauty
        invariant !found ==> best_beauty == original_beauty
        invariant found ==> best_beauty > original_beauty
        invariant forall j :: 0 <= j < i ==> 
                    var new_L := L - columns[j].0 + columns[j].1;
                    var new_R := R - columns[j].1 + columns[j].0;
                    abs(new_L - new_R) <= best_beauty
        invariant forall j :: 0 <= j < |columns| ==> 
                    var new_L := L - columns[j].0 + columns[j].1;
                    var new_R := R - columns[j].1 + columns[j].0;
                    abs(new_L - new_R) <= best_beauty || best_beauty < abs(new_L - new_R)
    {
        var new_L := L - columns[i].0 + columns[i].1;
        var new_R := R - columns[i].1 + columns[i].0;
        var current_beauty := abs(new_L - new_R);
        
        if current_beauty > best_beauty {
            best_idx := i;
            best_beauty := current_beauty;
            found := true;
        } else if current_beauty == best_beauty && !found {
            best_idx := i;
        }
        
        i := i + 1;
    }
    
    if best_beauty > original_beauty {
        result := best_idx + 1;
        assert forall j :: 0 <= j < |columns| ==> 
            var new_L := L - columns[j].0 + columns[j].1;
            var new_R := R - columns[j].1 + columns[j].0;
            abs(new_L - new_R) <= best_beauty;
    } else {
        result := 0;
        assert forall j :: 0 <= j < |columns| ==> 
            var new_L := L - columns[j].0 + columns[j].1;
            var new_R := R - columns[j].1 + columns[j].0;
            abs(new_L - new_R) <= original_beauty;
    }
}
// </vc-code>

