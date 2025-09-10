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
lemma MaxExistsInSeq(s: seq<int>)
    requires |s| >= 1
    ensures exists max_val :: max_val in s && (forall v :: v in s ==> v <= max_val)
{
    if |s| == 1 {
        assert s[0] in s;
        assert forall v :: v in s ==> v == s[0];
    } else {
        MaxExistsInSeq(s[1..]);
        var tail_max :| tail_max in s[1..] && (forall v :: v in s[1..] ==> v <= tail_max);
        if s[0] >= tail_max {
            assert s[0] in s;
            assert forall v :: v in s ==> v <= s[0];
        } else {
            assert tail_max in s;
            assert forall v :: v in s ==> v <= tail_max;
        }
    }
}

lemma MinExistsInSeq(s: seq<int>)
    requires |s| >= 1
    ensures exists min_val :: min_val in s && (forall v :: v in s ==> v >= min_val)
{
    if |s| == 1 {
        assert s[0] in s;
        assert forall v :: v in s ==> v == s[0];
    } else {
        MinExistsInSeq(s[1..]);
        var tail_min :| tail_min in s[1..] && (forall v :: v in s[1..] ==> v >= tail_min);
        if s[0] <= tail_min {
            assert s[0] in s;
            assert forall v :: v in s ==> v >= s[0];
        } else {
            assert tail_min in s;
            assert forall v :: v in s ==> v >= tail_min;
        }
    }
}

function FindMax(s: seq<int>): int
    requires |s| >= 1
    ensures FindMax(s) in s
    ensures forall v :: v in s ==> v <= FindMax(s)
{
    if |s| == 1 then s[0]
    else 
        var tail_max := FindMax(s[1..]);
        if s[0] >= tail_max then s[0] else tail_max
}

function FindMin(s: seq<int>): int
    requires |s| >= 1
    ensures FindMin(s) in s
    ensures forall v :: v in s ==> v >= FindMin(s)
{
    if |s| == 1 then s[0]
    else 
        var tail_min := FindMin(s[1..]);
        if s[0] <= tail_min then s[0] else tail_min
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
    
    assert |combined_x| >= 1;
    assert |combined_y| >= 1;
    
    MaxExistsInSeq(combined_x);
    MinExistsInSeq(combined_y);
    
    var max_x := FindMax(combined_x);
    var min_y := FindMin(combined_y);
    
    if max_x < min_y {
        assert max_x in combined_x;
        assert forall v :: v in combined_x ==> v <= max_x;
        assert min_y in combined_y;
        assert forall v :: v in combined_y ==> v >= min_y;
        assert max_x < min_y;
        assert AgreementPossible(n, m, x, y, xx, yy);
        result := "No War";
    } else {
        assert max_x >= min_y;
        
        // Prove that agreement is not possible
        forall max_val | max_val in combined_x && (forall v :: v in combined_x ==> v <= max_val)
        ensures !(exists min_val :: min_val in combined_y && 
                                   (forall v :: v in combined_y ==> v >= min_val) &&
                                   max_val < min_val)
        {
            assert max_val >= max_x;
            forall min_val | min_val in combined_y && (forall v :: v in combined_y ==> v >= min_val)
            ensures !(max_val < min_val)
            {
                assert min_val <= min_y;
                assert max_val >= max_x >= min_y >= min_val;
            }
        }
        
        assert !AgreementPossible(n, m, x, y, xx, yy);
        result := "War";
    }
}
// </vc-code>

