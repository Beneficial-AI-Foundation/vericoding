predicate ValidInput(n: int, m: int, d: int, matrix: seq<seq<int>>)
{
    n > 0 && m > 0 && d > 0 &&
    |matrix| == n &&
    (forall i :: 0 <= i < n ==> |matrix[i]| == m) &&
    (forall i, j :: 0 <= i < n && 0 <= j < m ==> matrix[i][j] > 0)
}

predicate AllSameRemainder(matrix: seq<seq<int>>, d: int)
    requires ValidInput(|matrix|, if |matrix| > 0 then |matrix[0]| else 0, d, matrix)
{
    forall i, j, k, l :: 0 <= i < |matrix| && 0 <= j < |matrix[0]| && 
                        0 <= k < |matrix| && 0 <= l < |matrix[0]| ==>
        matrix[i][j] % d == matrix[k][l] % d
}

function flatten(matrix: seq<seq<int>>): seq<int>
{
    if |matrix| == 0 then []
    else matrix[0] + flatten(matrix[1..])
}

function divideSequenceByD(s: seq<int>, d: int): seq<int>
    requires d > 0
{
    if |s| == 0 then []
    else [s[0] / d] + divideSequenceByD(s[1..], d)
}

function sumAbsDifferencesFromTarget(s: seq<int>, target: int): int
{
    if |s| == 0 then 0
    else (if s[0] >= target then s[0] - target else target - s[0]) + sumAbsDifferencesFromTarget(s[1..], target)
}

function minimumOperationsToMakeEqual(simplified: seq<int>): int
    requires |simplified| > 0
{
    var minVal := seqMin(simplified);
    var maxVal := seqMax(simplified);
    minOpsInRange(simplified, minVal, maxVal)
}

// <vc-helpers>
function seqMin(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] >= seqMin(s)
    ensures exists i :: 0 <= i < |s| && s[i] == seqMin(s)
{
    if |s| == 1 then s[0]
    else if s[0] <= seqMin(s[1..]) then s[0] else seqMin(s[1..])
}

function seqMax(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= seqMax(s)
    ensures exists i :: 0 <= i < |s| && s[i] == seqMax(s)
{
    if |s| == 1 then s[0]
    else if s[0] >= seqMax(s[1..]) then s[0] else seqMax(s[1..])
}

function minOpsInRange(s: seq<int>, low: int, high: int): int
    requires |s| > 0
    requires low <= high
    requires forall i :: 0 <= i < |s| ==> low <= s[i] <= high
{
    if low == high then sumAbsDifferencesFromTarget(s, low)
    else 
        var halfway := low + (high - low) / 2;
        var candidate1 := sumAbsDifferencesFromTarget(s, halfway);
        var candidate2 := sumAbsDifferencesFromTarget(s, halfway + 1);
        if candidate1 < candidate2 then candidate1 else candidate2
}

lemma distributive_property_div_mod(a: int, b: int)
    requires b > 0
    ensures (a / b) * b + (a % b) == a
{
    calc {
        (a / b) * b + (a % b);
        { assert a == (a / b) * b + (a % b); }
        a
    }
}

lemma mod_is_non_negative_and_less_than_divisor(a: int, b: int)
    requires b > 0
    ensures 0 <= a % b < b
{
    // Built-in property of Dafny's integer modulo
}

lemma all_elements_same_remainder_implies_flatten_has_same_remainder(matrix: seq<seq<int>>, d: int)
    requires ValidInput(|matrix|, |matrix[0]|, d, matrix)
    requires AllSameRemainder(matrix, d)
    ensures forall i, j :: 0 <= i < |matrix| && 0 <= j < |matrix[0]| ==> matrix[i][j] % d == matrix[0][0] % d
{
    var n := |matrix|;
    var m := |matrix[0]|;
    forall i, j | 0 <= i < n && 0 <= j < m
        ensures matrix[i][j] % d == matrix[0][0] % d
    {
        assert matrix[i][j] % d == matrix[0][0] % d by {
            assert AllSameRemainder(matrix, d);
        }
    }
}

lemma simplified_sequence_properties_helper(matrix: seq<seq<int>>, d: int)
    requires ValidInput(|matrix|, |matrix[0]|, d, matrix)
    requires AllSameRemainder(matrix, d)
    ensures {
        var flat := flatten(matrix);
        var simplified := divideSequenceByD(flat, d);
        |simplified| == |matrix| * |matrix[0]|
    }
{
    var n := |matrix|;
    var m := |matrix[0]|;
    assert |flatten(matrix)| == n * m;
    assert |divideSequenceByD(flatten(matrix), d)| == |flatten(matrix)|;
}

lemma divideSequenceByD_preserves_length(s: seq<int>, d: int)
    requires d > 0
    ensures |divideSequenceByD(s, d)| == |s|
{
    if |s| == 0 {
        assert divideSequenceByD(s, d) == [];
    } else {
        calc {
            |divideSequenceByD(s, d)|;
            == { assert divideSequenceByD(s, d) == [s[0] / d] + divideSequenceByD(s[1..], d); }
            1 + |divideSequenceByD(s[1..], d)|;
            == { divideSequenceByD_preserves_length(s[1..], d); }
            1 + |s[1..]|;
            == { assert |s| == 1 + |s[1..]|; }
            |s|
        }
    }
}

lemma flatten_matrix_has_nm_elements(matrix: seq<seq<int>>)
    requires ValidInput(|matrix|, |matrix[0]|, 1, matrix) // dummy d > 0
    ensures |flatten(matrix)| == |matrix| * |matrix[0]|
{
    var n := |matrix|;
    var m := |matrix[0]|;
    if n == 0 {
        assert flatten(matrix) == [];
    } else {
        calc {
            |flatten(matrix)|;
            == { assert flatten(matrix) == matrix[0] + flatten(matrix[1..]); }
            |matrix[0]| + |flatten(matrix[1..])|;
            == { assert |matrix[0]| == m; }
            m + |flatten(matrix[1..])|;
            == { flatten_matrix_has_nm_elements(matrix[1..]); }
            m + (n - 1) * m;
            ==
            n * m
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, d: int, matrix: seq<seq<int>>) returns (result: int)
    requires ValidInput(n, m, d, matrix)
    ensures result == -1 <==> !AllSameRemainder(matrix, d)
    ensures result >= 0 ==> AllSameRemainder(matrix, d)
    ensures result >= 0 ==> (var flat := flatten(matrix); var simplified := divideSequenceByD(flat, d); result == minimumOperationsToMakeEqual(simplified))
// </vc-spec>
// <vc-code>
{
    if !AllSameRemainder(matrix, d) {
        return -1;
    }

    var flat := flatten(matrix);
    assert |flat| == n * m by {
        flatten_matrix_has_nm_elements(matrix);
    }

    var simplified := divideSequenceByD(flat, d);
    assert |simplified| == |flat| == n * m by {
        divideSequenceByD_preserves_length(flat, d);
    }
    
    return minimumOperationsToMakeEqual(simplified);
}
// </vc-code>

