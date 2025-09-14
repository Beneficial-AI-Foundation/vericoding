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
    
    // Prove the second postcondition
    forall x, y | 0 <= x < y < |s|
        ensures s[x] <= maxVal || s[y] <= maxVal
    {
        if y == x + 1 {
            // x and y are consecutive
            assert max(s[x], s[y]) <= maxVal;
            assert s[x] <= maxVal || s[y] <= maxVal;
        } else {
            // x and y are not consecutive, so x+1 exists and x < x+1 < y
            assert x + 1 < y;
            assert max(s[x], s[x+1]) <= maxVal;
            if s[x] <= maxVal {
                assert s[x] <= maxVal || s[y] <= maxVal;
            } else {
                // s[x] > maxVal, so s[x+1] must be <= maxVal
                assert s[x+1] <= maxVal;
                // Now consider the pair (x+1, y)
                if y == x + 2 {
                    assert max(s[x+1], s[y]) <= maxVal;
                    assert s[y] <= maxVal;
                } else {
                    // We can continue this reasoning, but a simpler approach:
                    // Since s[x] > maxVal and max(s[x], s[x+1]) <= maxVal,
                    // we have s[x+1] <= maxVal < s[x], which is a contradiction
                    // Therefore s[x] <= maxVal must hold
                    assert false;
                }
            }
        }
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

