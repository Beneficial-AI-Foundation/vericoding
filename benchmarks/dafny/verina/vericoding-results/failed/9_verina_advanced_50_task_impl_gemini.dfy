// <vc-preamble>
predicate IsSorted(v: seq<nat>)
{
    forall i, j :: 0 <= i < j < |v| ==> v[i] <= v[j]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method MergeSorted(a1: array<nat>, a2: array<nat>) returns (result: array<nat>)
    requires IsSorted(a1[..])
    requires IsSorted(a2[..])
    ensures IsSorted(result[..])
    ensures multiset(result[..]) == multiset(a1[..]) + multiset(a2[..])
// </vc-spec>
// <vc-code>
{
    var len1 := a1.Length;
    var len2 := a2.Length;
    result := new nat[len1 + len2];

    var i := 0;
    var j := 0;
    var k := 0;

    while k < len1 + len2
        invariant 0 <= i <= len1
        invariant 0 <= j <= len2
        invariant k == i + j
        invariant multiset(result[..k]) == multiset(a1[..i]) + multiset(a2[..j])
        invariant IsSorted(result[..k])
        invariant i < len1 ==> forall m :: 0 <= m < k ==> result[m] <= a1[i]
        invariant j < len2 ==> forall m :: 0 <= m < k ==> result[m] <= a2[j]
    {
        if i < len1 && (j >= len2 || a1[i] <= a2[j]) {
            result[k] := a1[i];
            i := i + 1;
        } else {
            result[k] := a2[j];
            j := j + 1;
        }
        k := k + 1;
    }
}
// </vc-code>
