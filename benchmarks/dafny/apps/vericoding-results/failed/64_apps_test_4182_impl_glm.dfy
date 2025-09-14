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
lemma AgreementEquivalence(n: int, m: int, x: int, y: int, xx: seq<int>, yy: seq<int>, max_val_x: int, min_val_y: int)
    requires ValidInput(n, m, x, y, xx, yy)
    requires (forall a :: a in xx + [x] ==> a <= max_val_x)
    requires max_val_x in xx + [x]
    requires (forall b :: b in yy + [y] ==> b >= min_val_y)
    requires min_val_y in yy + [y]
    ensures AgreementPossible(n, m, x, y, xx, yy) <==> (max_val_x < min_val_y)
{
    if AgreementPossible(n, m, x, y, xx, yy) {
        var combined_x := xx + [x];
        var combined_y := yy + [y];
        var max_val :| max_val in combined_x && (forall v :: v in combined_x ==> v <= max_val);
        var min_val :| min_val in combined_y && (forall v :: v in combined_y ==> v >= min_val) && max_val < min_val;
        assert max_val <= max_val_x by { 
            assert max_val in combined_x;
        }
        assert min_val_y <= min_val by {
            assert min_val in combined_y;
        }
        assert max_val_x == max_val by {
            assert max_val_x <= max_val; 
        }
        assert min_val_y == min_val by {
            assert min_val <= min_val_y;
        }
        assert max_val_x < min_val_y;
    } else {
        if max_val_x < min_val_y {
            var combined_x := xx + [x];
            var combined_y := yy + [y];
            assert AgreementPossible(n, m, x, y, xx, yy) by {
                assert max_val_x in combined_x;
                assert min_val_y in combined_y;
            }
            assert false;
        }
    }
}

lemma MaxExists(s: seq<int>) returns (max_val: int)
    requires |s| > 0
    ensures max_val in s && forall i :: i in s ==> i <= max_val
{
    var i := 0;
    max_val := s[0];
    while i < |s|
        invariant 0 <= i <= |s|
        invariant max_val in s[0..i]
        invariant forall j :: j in s[0..i] ==> j <= max_val
    {
        if s[i] > max_val {
            max_val := s[i];
        }
        i := i + 1;
    }
}

lemma MinExists(s: seq<int>) returns (min_val: int)
    requires |s| > 0
    ensures min_val in s && forall i :: i in s ==> i >= min_val
{
    var i := 0;
    min_val := s[0];
    while i < |s|
        invariant 0 <= i <= |s|
        invariant min_val in s[0..i]
        invariant forall j :: j in s[0..i] ==> j >= min_val
    {
        if s[i] < min_val {
            min_val := s[i];
        }
        i := i + 1;
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
    var mx := MaxExists(combined_x);
    var mn := MinExists(combined_y);
    AgreementEquivalence(n, m, x, y, xx, yy, mx, mn);
    if mx < mn {
        return "No War";
    } else {
        return "War";
    }
}
// </vc-code>

