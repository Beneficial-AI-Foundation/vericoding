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
lemma sum_left_property(columns: seq<(int, int)>, i: int)
    requires ValidInput(columns)
    requires 0 <= i < |columns|
    ensures sum_left(columns[..i]) + columns[i].0 + sum_left(columns[i+1..]) == sum_left(columns)
{
    if i == 0 {
        assert columns[..0] == [];
        assert columns[1..] == columns[i+1..];
        assert sum_left(columns[..0]) == 0;
        assert sum_left(columns) == columns[0].0 + sum_left(columns[1..]);
    } else {
        assert columns == [columns[0]] + columns[1..];
        assert columns[..i] == [columns[0]] + columns[1..][..i-1];
        assert columns[1..][..i-1] == columns[1..i];
        sum_left_property(columns[1..], i-1);
        assert sum_left(columns[1..][..i-1]) + columns[1..][i-1].0 + sum_left(columns[1..][i..]) == sum_left(columns[1..]);
        assert columns[1..][i-1] == columns[i];
        assert columns[1..][i..] == columns[i+1..];
        assert sum_left(columns[1..i]) + columns[i].0 + sum_left(columns[i+1..]) == sum_left(columns[1..]);
        assert sum_left(columns[..i]) == columns[0].0 + sum_left(columns[1..i]);
        assert sum_left(columns) == columns[0].0 + sum_left(columns[1..]);
    }
}

lemma sum_right_property(columns: seq<(int, int)>, i: int)
    requires ValidInput(columns)
    requires 0 <= i < |columns|
    ensures sum_right(columns[..i]) + columns[i].1 + sum_right(columns[i+1..]) == sum_right(columns)
{
    if i == 0 {
        assert columns[..0] == [];
        assert columns[1..] == columns[i+1..];
        assert sum_right(columns[..0]) == 0;
        assert sum_right(columns) == columns[0].1 + sum_right(columns[1..]);
    } else {
        assert columns == [columns[0]] + columns[1..];
        assert columns[..i] == [columns[0]] + columns[1..][..i-1];
        assert columns[1..][..i-1] == columns[1..i];
        sum_right_property(columns[1..], i-1);
        assert sum_right(columns[1..][..i-1]) + columns[1..][i-1].1 + sum_right(columns[1..][i..]) == sum_right(columns[1..]);
        assert columns[1..][i-1] == columns[i];
        assert columns[1..][i..] == columns[i+1..];
        assert sum_right(columns[1..i]) + columns[i].1 + sum_right(columns[i+1..]) == sum_right(columns[1..]);
        assert sum_right(columns[..i]) == columns[0].1 + sum_right(columns[1..i]);
        assert sum_right(columns) == columns[0].1 + sum_right(columns[1..]);
    }
}

function beauty_after_swap(columns: seq<(int, int)>, i: int): int
    requires ValidInput(columns)
    requires 0 <= i < |columns|
{
    var L := sum_left(columns);
    var R := sum_right(columns);
    var new_L := L - columns[i].0 + columns[i].1;
    var new_R := R - columns[i].1 + columns[i].0;
    abs(new_L - new_R)
}

lemma beauty_equivalence(columns: seq<(int, int)>, i: int)
    requires ValidInput(columns)
    requires 0 <= i < |columns|
    ensures var L := sum_left(columns);
            var R := sum_right(columns);
            var new_L := L - columns[i].0 + columns[i].1;
            var new_R := R - columns[i].1 + columns[i].0;
            abs(new_L - new_R) == beauty_after_swap(columns, i)
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
    
    var best_idx := -1;
    var best_beauty := original_beauty;
    var i := 0;
    
    while i < |columns|
        invariant 0 <= i <= |columns|
        invariant best_idx == -1 ==> best_beauty == original_beauty
        invariant best_idx != -1 ==> 0 <= best_idx < i && best_beauty == beauty_after_swap(columns, best_idx)
        invariant best_idx != -1 ==> best_beauty > original_beauty
        invariant forall j :: 0 <= j < i ==> beauty_after_swap(columns, j) <= best_beauty
    {
        beauty_equivalence(columns, i);
        var new_L := L - columns[i].0 + columns[i].1;
        var new_R := R - columns[i].1 + columns[i].0;
        var new_beauty := abs(new_L - new_R);
        
        if new_beauty > best_beauty {
            best_idx := i;
            best_beauty := new_beauty;
        }
        
        i := i + 1;
    }
    
    if best_idx == -1 {
        forall j | 0 <= j < |columns|
            ensures var new_L := L - columns[j].0 + columns[j].1;
                    var new_R := R - columns[j].1 + columns[j].0;
                    abs(new_L - new_R) <= original_beauty
        {
            beauty_equivalence(columns, j);
            assert beauty_after_swap(columns, j) <= best_beauty;
            assert best_beauty == original_beauty;
        }
        return 0;
    } else {
        forall j | 0 <= j < |columns|
            ensures var new_L := L - columns[j].0 + columns[j].1;
                    var new_R := R - columns[j].1 + columns[j].0;
                    abs(new_L - new_R) <= best_beauty
        {
            beauty_equivalence(columns, j);
            assert beauty_after_swap(columns, j) <= best_beauty;
        }
        return best_idx + 1;
    }
}
// </vc-code>

