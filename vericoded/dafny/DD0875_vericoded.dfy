function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}

// <vc-helpers>
lemma MaxTransitive(m: int, numbers: seq<int>, newNum: int)
    requires numbers != []
    requires isMax(m, numbers)
    ensures isMax(if newNum > m then newNum else m, numbers + [newNum])
{
    var newMax := if newNum > m then newNum else m;
    assert newMax in (numbers + [newNum]);
    forall i | 0 <= i < |numbers + [newNum]|
        ensures (numbers + [newNum])[i] <= newMax
    {
        if i < |numbers| {
            assert (numbers + [newNum])[i] == numbers[i];
            assert numbers[i] <= m;
            if newNum > m {
                assert numbers[i] <= m < newNum == newMax;
            } else {
                assert numbers[i] <= m == newMax;
            }
        } else {
            assert i == |numbers|;
            assert (numbers + [newNum])[i] == newNum;
            if newNum > m {
                assert newNum == newMax;
            } else {
                assert newNum <= m == newMax;
            }
        }
    }
}
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
// </vc-spec>
// <vc-code>
{
    result := [numbers[0]];
    var currentMax := numbers[0];
    
    var i := 1;
    while i < |numbers|
        invariant 1 <= i <= |numbers|
        invariant |result| == i
        invariant currentMax == result[i-1]
        invariant isMax(currentMax, numbers[0..i])
        invariant forall j :: 0 < j < i ==> isMax(result[j], numbers[0..(j+1)])
    {
        if numbers[i] > currentMax {
            currentMax := numbers[i];
        }
        
        assert numbers[0..i] + [numbers[i]] == numbers[0..(i+1)];
        MaxTransitive(result[i-1], numbers[0..i], numbers[i]);
        
        result := result + [currentMax];
        i := i + 1;
    }
}
// </vc-code>

