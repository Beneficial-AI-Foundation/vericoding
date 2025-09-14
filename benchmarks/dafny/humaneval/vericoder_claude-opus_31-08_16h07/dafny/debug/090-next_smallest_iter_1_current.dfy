datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma MaxInPairs(s: seq<int>, maxVal: int)
    requires |s| >= 2
    requires exists i :: 0 <= i < |s| - 1 && max(s[i], s[i+1]) == maxVal
    requires forall i :: 0 <= i < |s| - 1 ==> max(s[i], s[i+1]) <= maxVal
    ensures exists x :: 0 <= x < |s| && s[x] == maxVal
    ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= maxVal || s[y] <= maxVal
{
    var idx :| 0 <= idx < |s| - 1 && max(s[idx], s[idx+1]) == maxVal;
    if s[idx] >= s[idx+1] {
        assert s[idx] == maxVal;
    } else {
        assert s[idx+1] == maxVal;
    }
}

function max(a: int, b: int): int
{
    if a >= b then a else b
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
        return None;
    }
    
    var maxVal := max(s[0], s[1]);
    var i := 1;
    
    while i < |s| - 1
        invariant 1 <= i <= |s| - 1
        invariant exists j :: 0 <= j < i && max(s[j], s[j+1]) == maxVal
        invariant forall j :: 0 <= j < i ==> max(s[j], s[j+1]) <= maxVal
    {
        maxVal := max(maxVal, max(s[i], s[i+1]));
        i := i + 1;
    }
    
    MaxInPairs(s, maxVal);
    return Some(maxVal);
}
// </vc-code>

