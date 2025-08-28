datatype Option<T> = None | Some(T)


function getVal(mx : Option<int>) : int
    requires mx != None
{
    match mx {
        case Some(n) => n
    }
}
// pure-end
method rolling_max(s: seq<int>) returns (res: Option<int>) 
    // post-conditions-start
    ensures res == None <==> |s| < 2
    ensures res != None ==> exists x :: 0 <= x < |s| && s[x] == getVal(res)
    ensures forall x, y :: 0 <= x < y < |s| ==> s[x] <= getVal(res) || s[y] <= getVal(res)
    // post-conditions-end
{
    // impl-start
    if |s| < 2 {
        return None;
    }

    res := None;
    var mx := s[0];
    var i := 1;

    while i < |s| 
        // invariants-start
        invariant 0 <= i <= |s|
        invariant i > 1 ==> res != None
        invariant exists x :: 0 <= x < |s| && s[x] == mx
        invariant res != None ==> exists x :: 0 <= x < |s| && s[x] == getVal(res)
        invariant i == 1 ==> res == None
        invariant i > 1 ==> getVal(res) <= mx
        invariant forall x :: 0 <= x < i ==> s[x] == mx || (res != None && s[x] <= getVal(res))
        invariant i > 1 ==> forall x, y :: 0 <= x < y < i ==> s[x] <= getVal(res) || s[y] <= getVal(res)
        // invariants-end
    {
        if s[i] > mx {
            res := Some(mx);
            mx := s[i];
        } else {
            match res {
                case None => res := Some(s[i]);
                case Some(n1) =>
                {
                    if (s[i] > n1) {
                        res := Some(s[i]);
                    }
                }
            }
        }
        i := i + 1;
    }
    // impl-end
}
