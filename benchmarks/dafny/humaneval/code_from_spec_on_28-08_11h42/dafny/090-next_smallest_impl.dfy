datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
lemma MaxValueExists(s: seq<int>, max_val: int)
    requires |s| >= 2
    requires exists i :: 0 <= i < |s| && s[i] == max_val
    requires forall i :: 0 <= i < |s| ==> s[i] <= max_val
    ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= max_val || s[y] <= max_val
{
    forall x, y | 0 <= x < y < |s|
        ensures s[x] <= max_val || s[y] <= max_val
    {
        assert s[x] <= max_val;
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
        return None;
    }
    
    var max_val := s[0];
    var i := 1;
    
    while i < |s|
        invariant 1 <= i <= |s|
        invariant exists j :: 0 <= j < i && s[j] == max_val
        invariant forall j :: 0 <= j < i ==> s[j] <= max_val
    {
        if s[i] > max_val {
            max_val := s[i];
        }
        i := i + 1;
    }
    
    MaxValueExists(s, max_val);
    return Some(max_val);
}
// </vc-code>
