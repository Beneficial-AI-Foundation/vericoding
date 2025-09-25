// <vc-preamble>
predicate CanWeighItem(w: int, m: int)
    requires w >= 2
{
    CanWeighItemFromState(w, m)
}

predicate CanWeighItemFromState(w: int, current_m: int)
    requires w >= 2
    decreases current_m
{
    if current_m <= 0 then
        true
    else
        var x := current_m % w;
        if x == 1 then
            CanWeighItemFromState(w, (current_m - 1) / w)
        else if x == w - 1 then
            CanWeighItemFromState(w, (current_m + 1) / w)
        else if x == 0 then
            CanWeighItemFromState(w, current_m / w)
        else
            false
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(w: int, m: int) returns (result: string)
    requires w >= 2 && w <= 1000000000 && m >= 1 && m <= 1000000000
    ensures result == "YES" || result == "NO"
    ensures result == "YES" <==> CanWeighItem(w, m)
// </vc-spec>
// <vc-code>
{
    var bb := CanWeighItem(w, m);
    var current_m := m;

    while current_m > 0 && bb
        decreases current_m
        invariant current_m >= 0
        invariant bb ==> CanWeighItemFromState(w, current_m)
        invariant !bb ==> !CanWeighItem(w, m)
    {
        var x := current_m % w;
        if x == 1 {
            current_m := current_m - 1;
        } else if x == w - 1 {
            current_m := current_m + 1;
        } else if x != 0 {
            bb := false;
        }
        current_m := current_m / w;
    }

    if bb {
        result := "YES";
    } else {
        result := "NO";
    }
}
// </vc-code>
