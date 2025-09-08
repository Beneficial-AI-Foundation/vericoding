Given a string q and an integer k, split the string into exactly k non-empty substrings
such that the substrings concatenate to form the original string and each substring 
starts with a different character (all first characters are distinct).

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

lemma concat_lemma(substrings: seq<seq<char>>, q: seq<char>, starts: seq<int>)
    requires |starts| == |substrings| + 1
    requires |starts| >= 1
    requires starts[0] == 0
    requires starts[|starts|-1] == |q|
    requires forall idx {:trigger starts[idx]} :: 0 <= idx < |starts| - 1 ==> 0 <= starts[idx] < starts[idx + 1] <= |q|
    requires forall idx :: 0 <= idx < |substrings| ==> 0 <= starts[idx] < starts[idx+1] <= |q| && substrings[idx] == q[starts[idx]..starts[idx+1]]
    ensures concat_seqs(substrings) == q
{
    if |substrings| == 0 {
        assert q == [];
    } else {
        var rest := substrings[1..];
        var rest_starts: seq<int> := [0];
        var idx := 1;
        while idx < |starts| - 1
            invariant 1 <= idx <= |starts| - 1
            invariant |rest_starts| == idx
            invariant forall i :: 0 <= i < idx ==> rest_starts[i] == starts[i+1] - starts[1]
        {
            rest_starts := rest_starts + [starts[idx+1] - starts[1]];
            idx := idx + 1;
        }
        var rest_q := q[starts[1]..];

        assert |rest_starts| == |rest| + 1;
        assert rest_starts[0] == 0;
        assert rest_starts[|rest_starts|-1] == |rest_q|;

        concat_lemma(rest, rest_q, rest_starts);

        calc {
            concat_seqs(substrings);
            substrings[0] + concat_seqs(rest);
            q[starts[0]..starts[1]] + rest_q;
            q[0..starts[1]] + q[starts[1]..];
            q;
        }
    }
}

method solve(k: int, q: seq<char>) returns (result: seq<seq<char>>)
    requires k >= 0
    requires |q| >= 0
    ensures k <= 0 || |q| == 0 ==> |result| == 0
    ensures k > 0 && |q| > 0 ==> (
        (|result| == 0) || ValidSplit(result, k, q)
    )
{
    if |q| == 0 || k <= 0 {
        return [];
    }

    var used: map<char, bool> := map[];
    var starts := [0];
    var cur := 0;
    var i := 1;

    used := used[q[0] := true];

    while i < |q| && cur < k - 1 
        invariant 1 <= i <= |q|
        invariant 0 <= cur <= k - 1
        invariant |starts| == cur + 1
        invariant forall idx :: 0 <= idx < |starts| ==> 0 <= starts[idx] < |q|
        invariant starts[0] == 0
        invariant forall idx {:trigger starts[idx]} :: 0 <= idx < |starts| - 1 ==> starts[idx] < starts[idx + 1]
        invariant cur >= 0 ==> i > starts[cur]
        invariant forall idx :: 0 <= idx < |starts| ==> q[starts[idx]] in used && used[q[starts[idx]]]
        invariant forall idx1, idx2 :: 0 <= idx1 < idx2 < |starts| ==> q[starts[idx1]] != q[starts[idx2]]
    {
        if q[i] !in used || !used[q[i]] {
            used := used[q[i] := true];
            starts := starts + [i];
            cur := cur + 1;
        }
        i := i + 1;
    }

    if cur < k - 1 {
        return [];
    } else {
        starts := starts + [|q|];
        var substrings: seq<seq<char>> := [];
        var j := 0;
        while j < |starts| - 1 
            invariant 0 <= j <= |starts| - 1
            invariant |substrings| == j
            invariant |starts| >= 2
            invariant |starts| == k + 1
            invariant forall idx {:trigger starts[idx]} :: 0 <= idx < |starts| - 1 ==> 0 <= starts[idx] < starts[idx + 1] <= |q|
            invariant forall idx :: 0 <= idx < j ==> |substrings[idx]| > 0
            invariant forall idx :: 0 <= idx < j ==> substrings[idx] == q[starts[idx]..starts[idx+1]]
            invariant starts[0] == 0 && starts[k] == |q|
            invariant forall idx1, idx2 :: 0 <= idx1 < idx2 < k ==> q[starts[idx1]] != q[starts[idx2]]
        {
            substrings := substrings + [q[starts[j]..starts[j+1]]];
            j := j + 1;
        }

        assert |substrings| == k;
        assert forall idx :: 0 <= idx < k ==> |substrings[idx]| > 0;
        assert forall idx1, idx2 :: 0 <= idx1 < idx2 < k ==> substrings[idx1][0] != substrings[idx2][0] by {
            forall idx1, idx2 | 0 <= idx1 < idx2 < k 
                ensures substrings[idx1][0] != substrings[idx2][0]
            {
                assert substrings[idx1] == q[starts[idx1]..starts[idx1+1]];
                assert substrings[idx2] == q[starts[idx2]..starts[idx2+1]];
                assert |substrings[idx1]| > 0 && |substrings[idx2]| > 0;
                assert substrings[idx1][0] == q[starts[idx1]];
                assert substrings[idx2][0] == q[starts[idx2]];
                assert q[starts[idx1]] != q[starts[idx2]];
            }
        }

        concat_lemma(substrings, q, starts);
        assert concat_seqs(substrings) == q;

        return substrings;
    }
}
