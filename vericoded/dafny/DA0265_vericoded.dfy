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
lemma sum_left_empty()
    ensures sum_left([]) == 0
{
}

lemma sum_right_empty()
    ensures sum_right([]) == 0
{
}

lemma sum_left_single(col: (int, int))
    ensures sum_left([col]) == col.0
{
}

lemma sum_right_single(col: (int, int))
    ensures sum_right([col]) == col.1
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
    if |columns| == 0 {
        return 0;
    }
    
    var L := sum_left(columns);
    var R := sum_right(columns);
    var original_beauty := abs(L - R);
    
    var best_beauty := original_beauty;
    var best_idx := -1;
    var i := 0;
    
    while i < |columns|
        invariant 0 <= i <= |columns|
        invariant best_beauty >= original_beauty
        invariant best_idx >= -1 && best_idx < i
        invariant if best_idx == -1 then
                    best_beauty == original_beauty &&
                    forall j :: 0 <= j < i ==> 
                        var new_L := L - columns[j].0 + columns[j].1;
                        var new_R := R - columns[j].1 + columns[j].0;
                        abs(new_L - new_R) <= original_beauty
                else
                    var best_L := L - columns[best_idx].0 + columns[best_idx].1;
                    var best_R := R - columns[best_idx].1 + columns[best_idx].0;
                    best_beauty == abs(best_L - best_R) &&
                    best_beauty > original_beauty &&
                    forall j :: 0 <= j < i ==> 
                        var new_L := L - columns[j].0 + columns[j].1;
                        var new_R := R - columns[j].1 + columns[j].0;
                        abs(new_L - new_R) <= best_beauty
    {
        var new_L := L - columns[i].0 + columns[i].1;
        var new_R := R - columns[i].1 + columns[i].0;
        var new_beauty := abs(new_L - new_R);
        
        if new_beauty > best_beauty {
            best_beauty := new_beauty;
            best_idx := i;
        }
        
        i := i + 1;
    }
    
    if best_idx == -1 {
        result := 0;
    } else {
        result := best_idx + 1;
    }
}
// </vc-code>

