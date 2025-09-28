// <vc-preamble>
function max(a: int, b: int): int
{
    if a >= b then a else b
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

function MaxRcur(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| <= 1 then
        s[0]
    else
        max(s[|s|-1], MaxRcur(s[..|s|-1]))
}

function MinRcur(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| <= 1 then
        s[0]
    else
        min(s[|s|-1], MinRcur(s[..|s|-1]))
}
// </vc-preamble>

// <vc-helpers>
predicate ValidElem(x: int)
{
  -1073741824 < x && x < 1073741823
}

function SumMinMaxOfSeq(s: seq<int>): int
    requires |s| > 0
{
  MaxRcur(s) + MinRcur(s)
}
// </vc-helpers>

// <vc-spec>
method SumMinMax(arr: array<int>) returns (sum: int)
    requires arr.Length > 0
    requires forall i :: 0 <= i < arr.Length ==> -1073741824 < arr[i] < 1073741823
    ensures sum == MaxRcur(arr[..]) + MinRcur(arr[..])
// </vc-spec>
// <vc-code>
{
  var s := arr[..];
  sum := MaxRcur(s) + MinRcur(s);
}
// </vc-code>
