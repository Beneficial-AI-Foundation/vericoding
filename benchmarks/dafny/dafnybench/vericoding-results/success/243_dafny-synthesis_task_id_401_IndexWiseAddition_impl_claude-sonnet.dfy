

// <vc-helpers>
lemma AdditionProperties(a: seq<int>, b: seq<int>, i: int)
    requires |a| == |b|
    requires 0 <= i < |a|
    ensures |a| == |b|
    ensures forall j :: 0 <= j < |a| ==> a[j] + b[j] == a[j] + b[j]
{
}

lemma SeqAdditionLength(a: seq<int>, b: seq<int>) returns (result: seq<int>)
    requires |a| == |b|
    ensures |result| == |a|
    ensures forall i :: 0 <= i < |result| ==> result[i] == a[i] + b[i]
{
    result := seq(|a|, i requires 0 <= i < |a| => a[i] + b[i]);
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
        invariant forall k :: 0 <= k < i ==> forall j :: 0 <= j < |result[k]| ==> result[k][j] == a[k][j] + b[k][j]
    {
        var row := seq(|a[i]|, j requires 0 <= j < |a[i]| => a[i][j] + b[i][j]);
        result := result + [row];
        i := i + 1;
    }
}
// </vc-code>

