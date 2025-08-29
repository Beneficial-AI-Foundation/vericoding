datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma MaxExistsLemma(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures exists j :: 0 <= j <= i && (forall k :: 0 <= k <= i ==> s[k] <= s[j])
{
    if i == 0 {
        assert s[0] <= s[0];
    } else {
        MaxExistsLemma(s, i-1);
        var j :| 0 <= j <= i-1 && (forall k :: 0 <= k <= i-1 ==> s[k] <= s[j]);
        if s[i] <= s[j] {
            assert forall k :: 0 <= k <= i ==> s[k] <= s[j];
        } else {
            assert forall k :: 0 <= k <= i ==> s[k] <= s[i];
        }
    }
}

lemma PostConditionLemma(s: seq<int>, max_val: int, max_idx: int)
    requires |s| >= 2
    requires 0 <= max_idx < |s|
    requires s[max_idx] == max_val
    requires forall k :: 0 <= k < |s| ==> s[k] <= max_val
    ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= max_val || s[y] <= max_val
{
}
// </vc-helpers>

// <vc-spec>
method rolling_max(s: seq<int>) returns (res: Option<int>) 
    // post-conditions-start
    ensures res == None <==> |s| < 2
    ensures res != None ==> exists x :: 0 <= x < |s| && s[x] == getVal(res)
    ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= getVal(res) || s[y] <= getVal(res)
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    if |s| < 2 {
        res := None;
        return;
    }
    
    MaxExistsLemma(s, |s| - 1);
    var max_idx :| 0 <= max_idx < |s| && (forall k :: 0 <= k < |s| ==> s[k] <= s[max_idx]);
    var max_val := s[max_idx];
    
    PostConditionLemma(s, max_val, max_idx);
    res := Some(max_val);
}
// </vc-code>

