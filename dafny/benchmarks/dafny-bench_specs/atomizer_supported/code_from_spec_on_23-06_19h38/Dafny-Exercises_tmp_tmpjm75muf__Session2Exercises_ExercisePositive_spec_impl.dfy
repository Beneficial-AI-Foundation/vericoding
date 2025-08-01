// ATOM 
predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

//IMPL mpositive
method mpositive(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    b := true;
    var i := 0;
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant b == positive(v[0..i])
    {
        if v[i] < 0 {
            b := false;
            return;
        }
        i := i + 1;
    }
}

//IMPL mpositive3
method mpositive3(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    b := true;
    var i := 0;
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant b == positive(v[0..i])
    {
        if v[i] < 0 {
            b := false;
            return;
        }
        i := i + 1;
    }
}

//IMPL mpositive4
method mpositive4(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    b := true;
    var i := 0;
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant b == positive(v[0..i])
    {
        if v[i] < 0 {
            b := false;
            return;
        }
        i := i + 1;
    }
}

//IMPL mpositivertl
method mpositivertl(v:array<int>) returns (b:bool)
ensures b==positive(v[0..v.Length])
{
    b := true;
    var i := 0;
    while i < v.Length
        invariant 0 <= i <= v.Length
        invariant b == positive(v[0..i])
    {
        if v[i] < 0 {
            b := false;
            return;
        }
        i := i + 1;
    }
}