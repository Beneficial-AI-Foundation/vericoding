function sumc(s: seq<int>, p: seq<bool>) : int
    requires |s| == |p|
    {
        if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
    }
function add_conditon(lst: seq<int>) : (p : seq<bool>)
    ensures |lst| == |p|
    {
        seq(|lst|, i requires 0 <= i < |lst| => lst[i] >= 0 && lst[i] % 2 == 1)
    }
function square_seq(lst: seq<int>) : (sq : seq<int>)
        ensures |sq| == |lst|
        ensures forall i :: 0 <= i < |lst| ==> sq[i] == lst[i] * lst[i]
    {
        seq(|lst|, i requires 0 <= i < |lst| => lst[i] * lst[i])
    }

// <vc-helpers>
function sumc_square_add_condition(lst: seq<int>): int
{
    if |lst| == 0 then 0
    else (if lst[0] >= 0 && lst[0] % 2 == 1 then lst[0] * lst[0] else 0) + sumc_square_add_condition(lst[1..])
}
// </vc-helpers>

// <vc-spec>
method double_the_difference(lst: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sumc(square_seq(lst), add_conditon(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var r_val := 0;
    for i := 0 to |lst|
        invariant 0 <= i <= |lst|
        invariant r_val == sumc_square_add_condition(lst[0..i])
    {
        if i < |lst| && lst[i] >= 0 && lst[i] % 2 == 1 {
            r_val := r_val + lst[i] * lst[i];
        }
    }
    return r_val;
}
// </vc-code>

