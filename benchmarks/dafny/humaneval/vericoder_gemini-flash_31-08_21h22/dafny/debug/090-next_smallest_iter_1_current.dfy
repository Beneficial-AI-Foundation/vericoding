datatype Option<T> = None | Some(T)
function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}

// <vc-helpers>
function max_of_two(a: int, b: int): int {
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
    } else {
        var current_max: int := s[0];
        var i: int := 1;
        while i < |s|
            invariant 1 <= i <= |s|
            invariant forall k :: 0 <= k < i ==> s[k] <= current_max
            invariant exists k :: 0 <= k < i && current_max == s[k]
        {
            current_max := max_of_two(current_max, s[i]);
            i := i + 1;
        }
        return Some(current_max);
    }
}
// </vc-code>

