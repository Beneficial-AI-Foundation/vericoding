// <vc-preamble>
datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}
// </vc-preamble>

// <vc-helpers>
function max_in_seq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= max_in_seq(s[1..])
         then s[0]
         else max_in_seq(s[1..])
}

lemma max_in_seq_is_maximum(s: seq<int>, i: int)
    requires |s| > 0
    requires 0 <= i < |s|
    ensures s[i] <= max_in_seq(s)
{
    if |s| == 1 {
        assert s[i] == s[0] == max_in_seq(s);
    } else {
        if i == 0 {
            if s[0] >= max_in_seq(s[1..]) {
                assert max_in_seq(s) == s[0];
            } else {
                assert max_in_seq(s) == max_in_seq(s[1..]);
                assert s[0] < max_in_seq(s[1..]);
            }
        } else {
            max_in_seq_is_maximum(s[1..], i-1);
            if s[0] >= max_in_seq(s[1..]) {
                assert max_in_seq(s) == s[0];
                assert s[i] == s[1..][i-1] <= max_in_seq(s[1..]) <= s[0];
            } else {
                assert max_in_seq(s) == max_in_seq(s[1..]);
            }
        }
    }
}

lemma max_in_seq_exists(s: seq<int>)
    requires |s| > 0
    ensures exists i :: 0 <= i < |s| && s[i] == max_in_seq(s)
{
    if |s| == 1 {
        assert s[0] == max_in_seq(s);
    } else {
        if s[0] >= max_in_seq(s[1..]) {
            assert s[0] == max_in_seq(s);
        } else {
            max_in_seq_exists(s[1..]);
            var j :| 0 <= j < |s[1..]| && s[1..][j] == max_in_seq(s[1..]);
            assert s[j+1] == max_in_seq(s);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method rolling_max(s: seq<int>) returns (res: Option<int>) 

    ensures res == None <==> |s| < 2
    ensures res != None ==> exists x :: 0 <= x < |s| && s[x] == getVal(res)
    ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= getVal(res) || s[y] <= getVal(res)
// </vc-spec>
// <vc-code>
{
    if |s| < 2 {
        res := None;
    } else {
        var max_val := max_in_seq(s);
        max_in_seq_exists(s);
        forall i | 0 <= i < |s|
            ensures s[i] <= max_val
        {
            max_in_seq_is_maximum(s, i);
        }
        res := Some(max_val);
    }
}
// </vc-code>
