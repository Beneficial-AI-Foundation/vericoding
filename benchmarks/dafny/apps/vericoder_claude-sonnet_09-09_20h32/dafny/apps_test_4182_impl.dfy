predicate ValidInput(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>)
{
    |xx| == n && |yy| == m && n >= 1 && m >= 1 && x < y
}

predicate AgreementPossible(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>)
    requires ValidInput(n, m, x, y, xx, yy)
{
    var combined_x := xx + [x];
    var combined_y := yy + [y];
    (exists max_val :: max_val in combined_x && 
                     (forall v :: v in combined_x ==> v <= max_val) &&
     exists min_val :: min_val in combined_y && 
                     (forall v :: v in combined_y ==> v >= min_val) &&
                     max_val < min_val)
}

// <vc-helpers>
function MaxInSeq(s: seq<int>): int
    requires |s| > 0
    ensures MaxInSeq(s) in s
    ensures forall v :: v in s ==> v <= MaxInSeq(s)
{
    if |s| == 1 then s[0]
    else if s[0] >= MaxInSeq(s[1..]) then 
        assert forall v :: v in s[1..] ==> v <= MaxInSeq(s[1..]);
        assert forall v :: v in s[1..] ==> v <= s[0];
        s[0]
    else 
        assert s[0] <= MaxInSeq(s[1..]);
        MaxInSeq(s[1..])
}

function MinInSeq(s: seq<int>): int
    requires |s| > 0
    ensures MinInSeq(s) in s
    ensures forall v :: v in s ==> v >= MinInSeq(s)
{
    if |s| == 1 then s[0]
    else if s[0] <= MinInSeq(s[1..]) then 
        assert forall v :: v in s[1..] ==> v >= MinInSeq(s[1..]);
        assert forall v :: v in s[1..] ==> v >= s[0];
        s[0]
    else 
        assert s[0] >= MinInSeq(s[1..]);
        MinInSeq(s[1..])
}

lemma MaxInSeqIsMax(s: seq<int>)
    requires |s| > 0
    ensures MaxInSeq(s) in s
    ensures forall v :: v in s ==> v <= MaxInSeq(s)
{
    if |s| == 1 {
        // base case
    } else {
        MaxInSeqIsMax(s[1..]);
        if s[0] >= MaxInSeq(s[1..]) {
            assert MaxInSeq(s) == s[0];
            assert forall v :: v in s[1..] ==> v <= MaxInSeq(s[1..]);
            assert forall v :: v in s[1..] ==> v <= s[0];
        } else {
            assert MaxInSeq(s) == MaxInSeq(s[1..]);
            assert s[0] < MaxInSeq(s[1..]);
            assert s[0] <= MaxInSeq(s);
        }
    }
}

lemma MinInSeqIsMin(s: seq<int>)
    requires |s| > 0
    ensures MinInSeq(s) in s
    ensures forall v :: v in s ==> v >= MinInSeq(s)
{
    if |s| == 1 {
        // base case
    } else {
        MinInSeqIsMin(s[1..]);
        if s[0] <= MinInSeq(s[1..]) {
            assert MinInSeq(s) == s[0];
            assert forall v :: v in s[1..] ==> v >= MinInSeq(s[1..]);
            assert forall v :: v in s[1..] ==> v >= s[0];
        } else {
            assert MinInSeq(s) == MinInSeq(s[1..]);
            assert s[0] > MinInSeq(s[1..]);
            assert s[0] >= MinInSeq(s);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>) returns (result: string)
    requires ValidInput(n, m, x, y, xx, yy)
    ensures result == "No War" || result == "War"
    ensures result == "No War" <==> AgreementPossible(n, m, x, y, xx, yy)
// </vc-spec>
// <vc-code>
{
    var combined_x := xx + [x];
    var combined_y := yy + [y];
    
    var max_x := MaxInSeq(combined_x);
    var min_y := MinInSeq(combined_y);
    
    MaxInSeqIsMax(combined_x);
    MinInSeqIsMin(combined_y);
    
    if max_x < min_y {
        result := "No War";
    } else {
        result := "War";
    }
}
// </vc-code>

