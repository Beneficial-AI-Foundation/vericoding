function concat_seqs(seqs: seq<seq<char>>): seq<char>
{
    if |seqs| == 0 then []
    else seqs[0] + concat_seqs(seqs[1..])
}

predicate ValidSplit(result: seq<seq<char>>, k: int, q: seq<char>)
{
    |result| == k &&
    (forall i :: 0 <= i < |result| ==> |result[i]| > 0) &&
    (forall i, j :: 0 <= i < j < |result| ==> result[i][0] != result[j][0]) &&
    concat_seqs(result) == q
}

// <vc-helpers>
lemma ConcatSeqsEmpty()
    ensures concat_seqs([]) == []
{
}

lemma ConcatSeqsSingle(s: seq<char>)
    ensures concat_seqs([s]) == s
{
    assert concat_seqs([s]) == s + concat_seqs([]);
}

lemma ConcatSeqsAppend(seqs: seq<seq<char>>, s: seq<char>)
    ensures concat_seqs(seqs + [s]) == concat_seqs(seqs) + s
{
    if |seqs| == 0 {
        assert seqs + [s] == [s];
        ConcatSeqsSingle(s);
    } else {
        assert (seqs + [s])[0] == seqs[0];
        assert (seqs + [s])[1..] == seqs[1..] + [s];
        ConcatSeqsAppend(seqs[1..], s);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(k: int, q: seq<char>) returns (result: seq<seq<char>>)
    requires k >= 0
    requires |q| >= 0
    ensures k <= 0 || |q| == 0 ==> |result| == 0
    ensures k > 0 && |q| > 0 ==> (
        (|result| == 0) || ValidSplit(result, k, q)
    )
// </vc-spec>
// <vc-code>
{
    if k <= 0 || |q| == 0 {
        return [];
    }
    
    var seen: set<char> := {};
    var currentGroup: seq<char> := [];
    result := [];
    
    var i := 0;
    while i < |q|
        invariant 0 <= i <= |q|
        invariant |result| <= k
        invariant |seen| <= k
        invariant forall j :: 0 <= j < |result| ==> |result[j]| > 0
        invariant forall j :: 0 <= j < |result| ==> result[j][0] in seen
        invariant forall j, l :: 0 <= j < l < |result| ==> result[j][0] != result[l][0]
        invariant concat_seqs(result) + currentGroup == q[..i]
        invariant |currentGroup| > 0 ==> currentGroup[0] in seen
        invariant |seen| == |result| + (if |currentGroup| > 0 then 1 else 0)
        invariant |currentGroup| > 0 ==> currentGroup[0] !in (set j | 0 <= j < |result| :: result[j][0])
    {
        var c := q[i];
        
        if c !in seen && |seen| < k {
            // Start a new group
            if |currentGroup| > 0 {
                ConcatSeqsAppend(result, currentGroup);
                result := result + [currentGroup];
            }
            seen := seen + {c};
            currentGroup := [c];
        } else {
            // Add to current group
            currentGroup := currentGroup + [c];
        }
        
        i := i + 1;
    }
    
    // Add the last group if it exists
    if |currentGroup| > 0 {
        ConcatSeqsAppend(result, currentGroup);
        result := result + [currentGroup];
    }
    
    // Check if we successfully created k groups
    if |result| != k {
        result := [];
    }
}
// </vc-code>

