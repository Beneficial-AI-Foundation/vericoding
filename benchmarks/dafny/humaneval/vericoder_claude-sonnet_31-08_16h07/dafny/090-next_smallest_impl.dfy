datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma MaxExists(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j < |s|
    ensures exists k :: i <= k <= j && forall m :: i <= m <= j ==> s[m] <= s[k]
{
    if i == j {
        assert s[i] <= s[i];
    } else {
        MaxExists(s, i, j-1);
        var k :| i <= k <= j-1 && forall m :: i <= m <= j-1 ==> s[m] <= s[k];
        if s[j] <= s[k] {
            assert forall m :: i <= m <= j ==> s[m] <= s[k];
        } else {
            assert forall m :: i <= m <= j ==> s[m] <= s[j];
        }
    }
}

lemma PostConditionHelper(s: seq<int>, maxVal: int)
    requires |s| >= 2
    requires exists x :: 0 <= x < |s| && s[x] == maxVal
    requires forall x :: 0 <= x < |s| ==> s[x] <= maxVal
    ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= maxVal || s[y] <= maxVal
{
    forall x, y | 0 <= x < y < |s|
        ensures s[x] <= maxVal || s[y] <= maxVal
    {
        assert s[x] <= maxVal;
    }
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
    
    MaxExists(s, 0, |s|-1);
    var maxIdx :| 0 <= maxIdx < |s| && forall i :: 0 <= i < |s| ==> s[i] <= s[maxIdx];
    
    res := Some(s[maxIdx]);
    
    PostConditionHelper(s, s[maxIdx]);
}
// </vc-code>

