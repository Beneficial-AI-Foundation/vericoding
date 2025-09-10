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
lemma MaxInSeq(s: seq<int>) returns (max_val: int)
    requires |s| > 0
    ensures max_val in s
    ensures forall v :: v in s ==> v <= max_val
{
    if |s| == 1 {
        max_val := s[0];
    } else {
        var sub_max := MaxInSeq(s[1..]);
        if s[0] > sub_max {
            max_val := s[0];
        } else {
            max_val := sub_max;
        }
    }
}

lemma MinInSeq(s: seq<int>) returns (min_val: int)
    requires |s| > 0
    ensures min_val in s
    ensures forall v :: v in s ==> v >= min_val
{
    if |s| == 1 {
        min_val := s[0];
    } else {
        var sub_min := MinInSeq(s[1..]);
        if s[0] < sub_min {
            min_val := s[0];
        } else {
            min_val := sub_min;
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
    
    if max_x < min_y {
        result := "No War";
    } else {
        result := "War";
    }
}
// </vc-code>

