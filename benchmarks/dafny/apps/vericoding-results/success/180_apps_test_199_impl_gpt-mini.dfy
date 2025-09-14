predicate ValidInput(n: int, s: int, v: seq<int>)
{
    n > 0 && |v| == n && s >= 0 && forall i :: 0 <= i < |v| ==> v[i] >= 0
}

function sum(v: seq<int>): int
{
    if |v| == 0 then 0
    else v[0] + sum(v[1..])
}

function minSeq(v: seq<int>): int
    requires |v| > 0
    ensures (forall i :: 0 <= i < |v| ==> v[i] >= 0) ==> minSeq(v) >= 0
{
    if |v| == 1 then v[0]
    else if v[0] <= minSeq(v[1..]) then v[0]
    else minSeq(v[1..])
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

// <vc-helpers>
lemma DivNonNeg(a: int, b: int)
    requires a >= 0 && b > 0
    ensures a / b >= 0
{
    // integer division of a nonnegative by a positive is nonnegative
    assert a / b >= 0;
}

lemma MinNonNeg(a: int, b: int)
    requires a >= 0 && b >= 0
    ensures min(a, b) >= 0
{
    if a <= b {
        assert min(a, b) == a;
        assert a >= 0;
    } else {
        assert min(a, b) == b;
        assert b >= 0;
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: int, v: seq<int>) returns (result: int)
    requires ValidInput(n, s, v)
    ensures sum(v) < s ==> result == -1
    ensures sum(v) >= s ==> result == min((sum(v) - s) / n, minSeq(v))
    ensures result == -1 || result >= 0
// </vc-spec>
// <vc-code>
{
  var tot := sum(v);
  if tot < s {
    result := -1;
    return;
  } else {
    // tot >= s and n > 0
    var a := tot - s;
    assert a >= 0;
    DivNonNeg(a, n);
    var q := a / n;
    var m := minSeq(v);
    // From ValidInput we have all elements nonnegative, so minSeq(v) >= 0
    assert forall i :: 0 <= i < |v| ==> v[i] >= 0;
    assert m >= 0;
    MinNonNeg(q, m);
    result := min(q, m);
    return;
  }
}
// </vc-code>

