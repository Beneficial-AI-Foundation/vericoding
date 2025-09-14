

// <vc-helpers>
lemma SequenceLengthLemma<T>(s: seq<T>, i: int)
    requires 0 <= i <= |s|
    ensures |s[0..i]| == i
{
}

lemma SequenceUpdateLemma<T>(s: seq<T>, i: int, e: T)
    requires 0 <= i <= |s|
    ensures |s + [e]| == |s| + 1
{
}

lemma SequenceIndexLemma<T>(s: seq<T>, i: int, e: T)
    requires 0 <= i == |s|
    ensures (s + [e])[i] == e
{
}

lemma SequenceSliceLemma<T>(s: seq<T>, i: int)
    requires 0 <= i <= |s|
    ensures s[0..i] + s[i..] == s
{
}
// </vc-helpers>

// <vc-spec>
method IndexWiseAddition(a: seq<seq<int>>, b: seq<seq<int>>) returns (result: seq<seq<int>>)
    requires |a| > 0 && |b| > 0
    requires |a| == |b|
    requires forall i :: 0 <= i < |a| ==> |a[i]| == |b[i]|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == |a[i]|
    ensures forall i :: 0 <= i < |result| ==> forall j :: 0 <= j < |result[i]| ==> result[i][j] == a[i][j] + b[i][j]
// </vc-spec>
// <vc-code>
{
    result := [];
    var i := 0;
    while i < |a|
        invariant 0 <= i <= |a|
        invariant |result| == i
        invariant forall k :: 0 <= k < i ==> |result[k]| == |a[k]|
        invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < |a[k]| ==> result[k][j] == a[k][j] + b[k][j]
    {
        var row := [];
        var j := 0;
        while j < |a[i]|
            invariant 0 <= j <= |a[i]|
            invariant |row| == j
            invariant forall l :: 0 <= l < j ==> row[l] == a[i][l] + b[i][l]
        {
            row := row + [a[i][j] + b[i][j]];
            j := j + 1;
        }
        result := result + [row];
        i := i + 1;
    }
}
// </vc-code>

