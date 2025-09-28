// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): converted to function method to aid prover */
predicate IsSorted(s: seq<int>){
    forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i+1]
}

/* helper modified by LLM (iteration 5): converted to function method to aid prover */
function method Insert(s: seq<int>, x: int): (res: seq<int>)
    requires IsSorted(s)
    ensures IsSorted(res)
    ensures multiset(res) == multiset(s) + multiset{x}
    ensures |res| == |s| + 1
    decreases |s|
{
    if s == [] {
        res := [x];
    } else if x <= s[0] {
        res := [x] + s;
    } else {
        var rest_inserted := Insert(s[1..], x);
        res := [s[0]] + rest_inserted;
    }
}

/* helper modified by LLM (iteration 5): converted to function method to aid prover */
function method Sort(s: seq<int>): (res: seq<int>)
    ensures IsSorted(res)
    ensures multiset(res) == multiset(s)
    ensures |res| == |s|
    decreases |s|
{
    if s == [] {
        res := [];
    } else {
        var sorted_rest := Sort(s[1..]);
        res := Insert(sorted_rest, s[0]);
    }
}

function Unique(s: seq<int>): seq<int>
    requires IsSorted(s)
    ensures IsSorted(Unique(s))
    ensures |s| > 0 ==> |Unique(s)| > 0 && Unique(s)[0] == s[0]
    ensures forall i :: 0 <= i < |Unique(s)| - 1 ==> Unique(s)[i] < Unique(s)[i+1]
    ensures forall x :: x in s <==> x in Unique(s)
    ensures |Unique(s)| <= |s|
{
    if |s| <= 1 then s
    else if s[0] == s[1] then Unique(s[1..])
    else [s[0]] + Unique(s[1..])
}
// </vc-helpers>

// <vc-spec>
method UniqueSorted(arr: array<int>) returns (result: array<int>)
    ensures result.Length <= arr.Length
    ensures forall i :: 0 <= i < result.Length - 1 ==> result[i] <= result[i + 1]
    ensures forall x :: x in arr[..] <==> x in result[..]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): no change to logic, relies on fixed helpers */
{
    var s := arr[..];
    var sorted_s := Sort(s);
    var unique_s := Unique(sorted_s);
    result := new int[|unique_s|](i requires 0 <= i < |unique_s| => unique_s[i]);
}
// </vc-code>
