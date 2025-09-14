function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}

// <vc-helpers>
lemma isMaxPreservation(m: int, s: seq<int>, x: int)
requires isMax(m, s)
requires x <= m
ensures isMax(m, s + [x])
{
    assert m in s + [x];
    assert forall i :: 0 <= i < |s + [x]| ==> (s + [x])[i] <= m;
}

lemma isMaxNewElement(x: int, s: seq<int>)
requires forall y :: y in s ==> y <= x
ensures isMax(x, s + [x])
{
    assert x in s + [x];
    forall i | 0 <= i < |s|
    ensures s[i] <= x
    {
        assert s[i] in s;
    }
    assert forall i {:trigger (s + [x])[i]} :: 0 <= i < |s| ==> (s + [x])[i] == s[i] <= x;
    assert (s + [x])[|s|] == x;
}

lemma maxExists(s: seq<int>)
requires s != []
ensures exists m :: isMax(m, s)
{
    var m := s[0];
    var i := 1;
    while i < |s|
    invariant 1 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] <= m
    invariant m in s[0..i]
    {
        if s[i] > m {
            m := s[i];
        }
        i := i + 1;
    }
    assert isMax(m, s);
}

lemma seqSliceEquivalence(numbers: seq<int>, i: int, j: int)
requires 0 < i <= |numbers|
requires 0 <= j < i
ensures numbers[0..i][j] == numbers[j]
{
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
    result := [];
    var i := 0;
    
    while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant |result| == i
    invariant forall j :: 0 < j < i ==> isMax(result[j], numbers[0..(j+1)])
    {
        var currentMax := numbers[0];
        var k := 1;
        
        while k <= i
        invariant 1 <= k <= i + 1
        invariant currentMax in numbers[0..(i+1)]
        invariant forall j :: 0 <= j < k ==> numbers[j] <= currentMax
        {
            if numbers[k] > currentMax {
                currentMax := numbers[k];
            }
            k := k + 1;
        }
        
        assert currentMax in numbers[0..(i+1)];
        assert forall j :: 0 <= j <= i ==> numbers[j] <= currentMax;
        forall j {:trigger numbers[0..(i+1)][j]} | 0 <= j < |numbers[0..(i+1)]|
        ensures numbers[0..(i+1)][j] <= currentMax
        {
            seqSliceEquivalence(numbers, i+1, j);
            assert numbers[0..(i+1)][j] == numbers[j];
            assert numbers[j] <= currentMax;
        }
        assert isMax(currentMax, numbers[0..(i+1)]);
        
        result := result + [currentMax];
        
        i := i + 1;
    }
}
// </vc-code>

