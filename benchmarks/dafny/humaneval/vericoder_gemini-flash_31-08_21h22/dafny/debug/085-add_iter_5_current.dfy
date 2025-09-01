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
    // This function is just a recursive definition, it does not strictly need `decreases` unless it's an inductive proof helper.
    // However, including it doesn't hurt.
    decreases |s|
{
    if |s| == 0 then 0
    else (if p[0] then s[0] else 0) + sumc_iterative(s[1..], p[1..])
}

lemma sumc_sum_property(s: seq<int>, p: seq<bool>, k: nat)
    requires 0 <= k <= |s|
    requires |s| == |p|
    ensures sumc(s, p) == sumc(s[..k], p[..k]) + sumc(s[k..], p[k..])
{
    if k == 0 {
        // Base case: sumc(s,p) == sumc(s[..0], p[..0]) + sumc(s[0..], p[0..])
        // sumc(s,p) == 0 + sumc(s,p)
    } else {
        sumc_sum_property(s[..k], p[..k], k-1);
        sumc_sum_property(s, p, k - 1);
    }
}

lemma sumc_iterative_sum_property(s: seq<int>, p: seq<bool>, k: nat)
    requires 0 <= k <= |s|
    requires |s| == |p|
    ensures sumc_iterative(s, p) == sumc_iterative(s[..k], p[..k]) + sumc_iterative(s[k..], p[k..])
{
    if k == 0 {
        // Base case: sumc_iterative(s,p) == sumc_iterative(s[..0], p[..0]) + sumc_iterative(s[0..], p[0..])
        // sumc_iterative(s,p) == 0 + sumc_iterative(s,p)
    } else {
        sumc_iterative_sum_property(s[..k], p[..k], k-1);
        sumc_iterative_sum_property(s, p, k - 1);
    }
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
        invariant sumc_iterative(v[..i], p_computed[..i]) == sumc(v[..i], p_computed[..i])
        invariant forall k :: 0 <= k < i ==> (p_computed[k] == (k % 2 == 1 && v[k] % 2 == 0))
    {
        if p_computed[i]
        {
            r_local := r_local + v[i];
        }
        i := i + 1;
        sumc_equals_sumc_iterative(v[..i], p_computed[..i]);
    }
    r := r_local;
    sumc_equals_sumc_iterative(v, p_computed);
    assert r == sumc_iterative(v, p_computed); // from loop invariant
    assert sumc_iterative(v, p_computed) == sumc(v, p_computed); // from `sumc_equals_sumc_iterative` lemma invocation
    assert r == sumc(v, p_computed);
    // The `add_conditon` in the postcondition uses the function from the preamble.
    // The `add_condition` helper function is identical to it.
    // So p_computed should be equal to add_conditon(v).
    assert p_computed == add_conditon(v);
}
// </vc-code>

// pure-end