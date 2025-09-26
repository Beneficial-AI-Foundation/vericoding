// <vc-preamble>
predicate chronologicallyValid(input: seq<(int, int)>)
{
    forall i :: 0 <= i < |input| ==>
        var x := input[i].0;
        var k := input[i].1;
        x == 0 || exists j :: 0 <= j < i && input[j].1 == k && input[j].0 >= x - 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: seq<(int, int)>) returns (result: string)
    requires forall i :: 0 <= i < |input| ==> input[i].1 >= 1 && input[i].1 <= 100000
    requires forall i :: 0 <= i < |input| ==> input[i].0 >= 0 && input[i].0 <= 100000
    requires |input| <= 100000
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> chronologicallyValid(input)
// </vc-spec>
// <vc-code>
{
    var n := |input|;
    var a := new int[100001];
    var i := 0;
    while i < 100001
        invariant 0 <= i <= 100001
        invariant forall j :: 0 <= j < i ==> a[j] == -1
    {
        a[i] := -1;
        i := i + 1;
    }

    var p := false;
    i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant p <==> (exists idx :: 0 <= idx < i && 
            (input[idx].0 > 0 && 
             (forall j :: 0 <= j < idx ==> input[j].1 != input[idx].1 || input[j].0 < input[idx].0 - 1)))
        invariant forall k :: 1 <= k <= 100000 ==> 
            (a[k] == -1 <==> (forall j :: 0 <= j < i ==> input[j].1 != k))
        invariant forall k :: 1 <= k <= 100000 ==> a[k] >= -1
        invariant forall k :: 1 <= k <= 100000 ==> a[k] != -1 ==>
            (exists j :: 0 <= j < i && input[j].1 == k && input[j].0 == a[k] &&
             (forall j' :: 0 <= j' < i && input[j'].1 == k ==> input[j'].0 <= a[k]))
    {
        var x := input[i].0;
        var k := input[i].1;
        if x > 0 && (a[k] == -1 || a[k] < x - 1) {
            p := true;
        }
        if a[k] == -1 {
            a[k] := x;
        } else {
            a[k] := if a[k] > x then a[k] else x;
        }
        i := i + 1;
    }

    if p {
        result := "NO";
    } else {
        result := "YES";
    }
}
// </vc-code>
