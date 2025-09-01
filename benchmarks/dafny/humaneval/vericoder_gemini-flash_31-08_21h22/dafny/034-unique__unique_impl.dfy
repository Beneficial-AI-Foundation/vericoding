method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function IsUniqueSorted(s: seq<int>): bool
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

function IsSubsequenceOf(s1: seq<int>, s2: seq<int>): bool
{
    forall x :: x in s1 ==> x in s2
}

function IsSupersetOf(s1: seq<int>, s2: seq<int>): bool
{
    forall x :: x in s2 ==> x in s1
}

ghost predicate UniqueElementsInPrefixReflected(s: seq<int>, result_seq: seq<int>, i: int)
  requires 0 <= i <= |s|
  requires forall k, l :: 0 <= k < l < |result_seq| ==> result_seq[k] < result_seq[l]
{
  forall x :: (exists k_first :: 0 <= k_first < i && s[k_first] == x && (forall k_prev :: 0 <= k_prev < k_first && s[k_prev] != x)) ==> x in result_seq
}

ghost predicate UniqueCheck(s: seq<int>, result_seq: seq<int>, i: int)
  requires 0 <= i <= |s|
  requires forall k, l :: 0 <= k < l < |result_seq| ==> result_seq[k] < result_seq[l]
{
  forall x :: (exists k_first :: 0 <= k_first < i && s[k_first] == x && (forall k_prev :: 0 <= k_prev < k_first && s[k_prev] != x)) ==> x in result_seq
}
// </vc-helpers>

// <vc-spec>
method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var result_seq: seq<int> := [];
    if |s| == 0 {
        return result_seq;
    }

    result_seq := result_seq + [s[0]];
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant forall k, l :: 0 <= k < l < |result_seq| ==> result_seq[k] < result_seq[l]
        invariant forall x :: x in result_seq ==> x in s[..i]
        invariant UniqueCheck(s, result_seq, i)
        invariant |result_seq| > 0 ==> result_seq[|result_seq|-1] <= s[i-1]
        invariant |result_seq| > 0 ==> (i < |s| ==> result_seq[|result_seq|-1] < s[i] || result_seq[|result_seq|-1] == s[i])
        decreases |s| - i
    {
        if s[i] > result_seq[|result_seq|-1] {
            result_seq := result_seq + [s[i]];
        } else {
            assert s[i] == result_seq[|result_seq|-1];
        }
        i := i + 1;
    }

    assert IsUniqueSorted(result_seq);
    assert IsSubsequenceOf(result_seq, s);

    forall x | x in s
    ensures x in result_seq
    {
        var first_occurrence_index: int := -1;
        for k := 0 to |s|
            invariant -1 <= first_occurrence_index < |s|
            invariant forall idx :: 0 <= idx < k && s[idx] == x ==> (first_occurrence_index != -1 && s[first_occurrence_index] == x)
        {
            if s[k] == x {
                if first_occurrence_index == -1 {
                    first_occurrence_index := k;
                }
            }
        }
        assert first_occurrence_index != -1; // x must be in s
        assert (exists k_first :: 0 <= k_first < |s| && s[k_first] == x && (forall k_prev :: 0 <= k_prev < k_first && s[k_prev] != x));
        
        // This assertion follows directly from the loop invariant UniqueCheck(s, result_seq, |s|)
        // because we have established that x has a first occurrence in s.
        assert x in result_seq; 
    }
    assert IsSupersetOf(s, result_seq); 

    return result_seq;
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}