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
lemma sumc_empty(s: seq<int>, p: seq<bool>)
    requires |s| == |p|
    ensures sumc(s, p) == 0
    decreases |s|
{
    if |s| != 0 {
        sumc_empty(s[1..], p[1..]);
    }
}

lemma sumc_nonempty(s: seq<int>, p: seq<bool>, i: int)
    requires |s| == |p|
    requires 0 <= i < |s|
    ensures sumc(s, p) == (if p[i] then s[i] else 0) + sumc(s[i+1..], p[i+1..]) + sumc(s[..i], p[..i])
    decreases |s|
{
    if i > 0 {
        sumc_nonempty(s[1..], p[1..], i-1);
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
    r := 0;
    var i := 0;
    while i < |v|
        invariant 0 <= i <= |v|
        invariant r == sumc(v[..i], add_conditon(v)[..i])
    {
        var p := add_conditon(v);
        if i % 2 == 1 && v[i] % 2 == 0 {
            r := r + v[i];
        }
        i := i + 1;
    }
}
// </vc-code>

// pure-end