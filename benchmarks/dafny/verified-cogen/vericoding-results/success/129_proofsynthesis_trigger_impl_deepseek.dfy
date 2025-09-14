// <vc-preamble>
function f(s: seq<int>, i: int): bool
    requires 0 <= i < |s|
{
    s[i] == i + 2
}
// </vc-preamble>

// <vc-helpers>
function f_helper(s: seq<int>, j: int): bool
    requires 0 <= j < |s|
{
    s[j] == j + 2
}

lemma f_helper_lemma(s: seq<int>, j: int)
    requires 0 <= j < |s|
    requires f(s, j)
    ensures s[j] == j + 2
{
}

lemma array_to_seq_lemma(arr: array<int>, j: int)
    requires 0 <= j < arr.Length
    ensures arr[..][j] == arr[j]
{
}
// </vc-helpers>

// <vc-spec>
method GetElementCheckProperty(arr: array<int>, i: int) returns (ret: int)
    requires arr.Length > 0
    requires 0 < i < arr.Length
    requires forall j :: 0 <= j < arr.Length ==> f(arr[..], j)
    ensures ret == i + 2
    ensures ret == arr[i]
// </vc-spec>
// <vc-code>
{
    ret := arr[i];
    assert arr[..][i] == arr[i] by { array_to_seq_lemma(arr, i); }
    assert f(arr[..], i) == (arr[..][i] == i + 2);
    assert f(arr[..], i) by { assert forall j :: 0 <= j < arr.Length ==> f(arr[..], j); }
    assert arr[..][i] == i + 2 by { f_helper_lemma(arr[..], i); }
}
// </vc-code>
