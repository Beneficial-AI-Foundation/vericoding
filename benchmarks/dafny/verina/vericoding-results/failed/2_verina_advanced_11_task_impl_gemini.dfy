// <vc-preamble>
function CountOccurrences(x: int, lst: seq<int>): nat
{
    |set i | 0 <= i < |lst| && lst[i] == x|
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): [added proof bodies] */
lemma CountOccurrencesAppendUnit(x: int, s: seq<int>, y: int)
    ensures CountOccurrences(x, s + [y]) == CountOccurrences(x, s) + (if x == y then 1 else 0)
{
    calc {
        CountOccurrences(x, s + [y]);
        |set i | 0 <= i < |s + [y]| && (s + [y])[i] == x|;
        | (set i | 0 <= i < |s| && (s + [y])[i] == x) + (set i | i == |s| && (s + [y])[i] == x) |;
        == { assert forall i :: 0 <= i < |s| ==> (s + [y])[i] == s[i]; }
        | (set i | 0 <= i < |s| && s[i] == x) + (set i | i == |s| && y == x) |;
        == { assert (set i | 0 <= i < |s| && s[i] == x) !! (set i | i == |s| && y == x); }
        |set i | 0 <= i < |s| && s[i] == x| + |set i | i == |s| && y == x|;
        CountOccurrences(x, s) + (if x == y then 1 else 0);
    }
}

method CountElement(x: int, s: seq<int>) returns (count: nat)
    ensures count == CountOccurrences(x, s)
{
    count := 0;
    var i: nat := 0;
    while i < |s|
        invariant 0 <= i <= |s|
        invariant count == CountOccurrences(x, s[..i])
    {
        CountOccurrencesAppendUnit(x, s[..i], s[i]);
        if s[i] == x {
            count := count + 1;
        }
        i := i + 1;
    }
}

/* helper modified by LLM (iteration 2): [added proof bodies] */
lemma TwoElementsCount(s: seq<int>, x: int, y: int)
    requires x != y
    ensures CountOccurrences(x, s) + CountOccurrences(y, s) <= |s|
{
    var indices_x := set i | 0 <= i < |s| && s[i] == x;
    var indices_y := set i | 0 <= i < |s| && s[i] == y;
    assert indices_x !! indices_y;
    var combined_indices := indices_x + indices_y;
    assert |combined_indices| == |indices_x| + |indices_y|;
    assert combined_indices <= (set i | 0 <= i < |s|);
    assert |combined_indices| <= |s|;

}

lemma UniqueMajority(s: seq<int>, m: int)
    requires CountOccurrences(m, s) > |s| / 2
    ensures forall x :: x != m ==> CountOccurrences(x, s) <= |s| / 2
{
    forall x | x != m ensures CountOccurrences(x, s) <= |s| / 2 {
        TwoElementsCount(s, x, m);
    }
}

/* helper modified by LLM (iteration 2): [added proof bodies] */
lemma InSeqIffCountPositive(s: seq<int>)
    ensures forall x :: x in s <==> CountOccurrences(x, s) > 0
{
    forall x ensures x in s <==> CountOccurrences(x, s) > 0 {
        if x in s {
            var i :| 0 <= i < |s| && s[i] == x;
            assert i in (set j | 0 <= j < |s| && s[j] == x);
            assert CountOccurrences(x, s) >= 1;
        } else {
            assert forall j :: 0 <= j < |s| ==> s[j] != x;
            assert (set j | 0 <= j < |s| && s[j] == x) == {};
            assert CountOccurrences(x, s) == 0;
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
    /* code modified by LLM (iteration 2): [added loop invariant and proof for no-majority case] */
    var n := lst.Length;
    if n == 0 {
        result := -1;
        return;
    }

    var lst_seq := lst[..];
    var i: nat := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> CountOccurrences(lst[k], lst_seq) <= n / 2
    {
        var current_element := lst[i];
        var count := CountElement(current_element, lst_seq);
        if count > n / 2 {
            UniqueMajority(lst_seq, current_element);
            result := current_element;
            return;
        }
        i := i + 1;
    }
    
    InSeqIffCountPositive(lst_seq);
    forall x ensures CountOccurrences(x, lst_seq) <= n / 2
    {
        if x in lst_seq {
            var k :| 0 <= k < n && lst[k] == x;
            assert CountOccurrences(lst[k], lst_seq) <= n/2;
        } else {
            assert CountOccurrences(x, lst_seq) == 0;
        }
    }
    
    result := -1;
}
// </vc-code>
