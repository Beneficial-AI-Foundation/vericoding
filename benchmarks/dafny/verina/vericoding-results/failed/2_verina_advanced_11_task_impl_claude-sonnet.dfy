// <vc-preamble>
function CountOccurrences(x: int, lst: seq<int>): nat
{
    |set i | 0 <= i < |lst| && lst[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed set union syntax error */
function IsMajorityElement(x: int, lst: seq<int>): bool
{
    var n := |lst|;
    CountOccurrences(x, lst) > n / 2
}

lemma DisjointSetsCardinality(x: int, y: int, lst: seq<int>)
    requires x != y
    ensures var x_indices := set i | 0 <= i < |lst| && lst[i] == x;
            var y_indices := set i | 0 <= i < |lst| && lst[i] == y;
            x_indices !! y_indices && |x_indices| + |y_indices| <= |lst|
{
    var x_indices := set i | 0 <= i < |lst| && lst[i] == x;
    var y_indices := set i | 0 <= i < |lst| && lst[i] == y;
    
    forall i | i in x_indices
        ensures i !in y_indices
    {
        assert lst[i] == x;
        assert lst[i] != y;
    }
    
    assert x_indices !! y_indices;
    assert x_indices <= set i | 0 <= i < |lst|;
    assert y_indices <= set i | 0 <= i < |lst|;
    assert |x_indices * y_indices| == |x_indices| + |y_indices|;
    assert x_indices * y_indices <= set i | 0 <= i < |lst|;
    assert |x_indices * y_indices| <= |lst|;
}

lemma MajorityElementUnique(lst: seq<int>, x: int, y: int)
    requires IsMajorityElement(x, lst)
    requires IsMajorityElement(y, lst)
    ensures x == y
{
    var n := |lst|;
    if x != y {
        DisjointSetsCardinality(x, y, lst);
        var x_count := CountOccurrences(x, lst);
        var y_count := CountOccurrences(y, lst);
        assert x_count > n / 2;
        assert y_count > n / 2;
        assert x_count + y_count > n;
        assert false;
    }
}

lemma CountOccurrencesSliceExtend(x: int, lst: seq<int>, i: int)
    requires 0 <= i < |lst|
    ensures CountOccurrences(x, lst[..i+1]) == 
            CountOccurrences(x, lst[..i]) + (if lst[i] == x then 1 else 0)
{
}

lemma CountOccurrencesCorrect(candidate: int, lst: seq<int>, count: nat)
    requires count == CountOccurrences(candidate, lst)
    ensures count > |lst| / 2 ==> IsMajorityElement(candidate, lst)
    ensures count <= |lst| / 2 ==> !IsMajorityElement(candidate, lst)
{
}

lemma NoMajorityImpliesAllBounded(lst: seq<int>, candidate: int)
    requires CountOccurrences(candidate, lst) <= |lst| / 2
    ensures forall x :: CountOccurrences(x, lst) <= |lst| / 2
{
    forall x
        ensures CountOccurrences(x, lst) <= |lst| / 2
    {
        if CountOccurrences(x, lst) > |lst| / 2 {
            assert IsMajorityElement(x, lst);
            assert CountOccurrences(candidate, lst) > |lst| / 2;
            assert false;
        }
    }
}
// </vc-helpers>

// <vc-spec>
method FindMajorityElement(lst: array<int>) returns (result: int)
    ensures var lst_seq := lst[..];
            var n := |lst_seq|;
            var majority := CountOccurrences(result, lst_seq) > n / 2 && 
                          forall x :: CountOccurrences(x, lst_seq) <= n / 2 || x == result;
            (result == -1 ==> forall x :: CountOccurrences(x, lst_seq) <= n / 2) &&
            (result != -1 ==> majority)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed loop invariants and added proper slice handling */
    var n := lst.Length;
    if n == 0 {
        result := -1;
        return;
    }
    
    var candidate := lst[0];
    var count := 1;
    
    var i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant 0 <= count
    {
        if lst[i] == candidate {
            count := count + 1;
        } else {
            count := count - 1;
            if count == 0 {
                candidate := lst[i];
                count := 1;
            }
        }
        i := i + 1;
    }
    
    var verify_count := 0;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant verify_count == CountOccurrences(candidate, lst[..i])
    {
        CountOccurrencesSliceExtend(candidate, lst[..], i);
        if lst[i] == candidate {
            verify_count := verify_count + 1;
        }
        i := i + 1;
    }
    
    assert lst[..] == lst[..n];
    assert verify_count == CountOccurrences(candidate, lst[..]);
    CountOccurrencesCorrect(candidate, lst[..], verify_count);
    
    if verify_count > n / 2 {
        result := candidate;
        assert IsMajorityElement(result, lst[..]);
        assert CountOccurrences(result, lst[..]) > n / 2;
        forall x | x != result
            ensures CountOccurrences(x, lst[..]) <= n / 2
        {
            if CountOccurrences(x, lst[..]) > n / 2 {
                MajorityElementUnique(lst[..], result, x);
            }
        }
    } else {
        result := -1;
        assert CountOccurrences(candidate, lst[..]) <= n / 2;
        NoMajorityImpliesAllBounded(lst[..], candidate);
    }
}
// </vc-code>
