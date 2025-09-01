function sumc(s: seq<int>, p: seq<bool>) : int
    requires |s| == |p|
    {
        if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
    }
function add_conditon(lst: seq<int>) : (p : seq<bool>)
    ensures |lst| == |p|
    {
        seq(|lst|, i requires 0 <= i < |lst| => i % 2 == 1 && lst[i] % 2 == 0)
    }

// <vc-helpers>
function add_condition(lst: seq<int>) : seq<bool>
    ensures |lst| == |add_condition(lst)|
{
    seq(|lst|, i requires 0 <= i < |lst| => i % 2 == 1 && lst[i] % 2 == 0)
}

function sumc_iterative(s: seq<int>, p: seq<bool>) : int
    requires |s| == |p|
    decreases |s|
{
    if |s| == 0 then 0
    else (if p[0] then s[0] else 0) + sumc_iterative(s[1..], p[1..])
}

lemma sumc_equals_sumc_iterative(s: seq<int>, p: seq<bool>)
    requires |s| == |p|
    ensures sumc(s, p) == sumc_iterative(s, p)
{
    if |s| == 0 {
        // Base case, both return 0
    } else {
        // Inductive step
        sumc_equals_sumc_iterative(s[1..], p[1..]);
    }
}
// </vc-helpers>

// <vc-spec>
method add(v: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sumc(v, add_conditon(v))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var r_local := 0;
    var p_computed := add_condition(v);
    var i := 0;
    while i < |v|
        invariant 0 <= i <= |v|
        invariant r_local == sumc_iterative(v[..i], p_computed[..i])
        invariant |p_computed| == |v|
    {
        if p_computed[i] then
            r_local := r_local + v[i];
        i := i + 1;
    }
    r := r_local;
    sumc_equals_sumc_iterative(v, p_computed);
    assert r == sumc(v, p_computed);
    assert p_computed == add_conditon(v); // This assertion might be redundant if add_condition is the exact implementation of add_conditon from the preamble.
}
// </vc-code>

// pure-end