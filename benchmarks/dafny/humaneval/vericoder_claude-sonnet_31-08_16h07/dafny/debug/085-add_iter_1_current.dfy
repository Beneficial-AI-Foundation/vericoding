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
lemma sumc_equivalence(s: seq<int>, p: seq<bool>, acc: int)
    requires |s| == |p|
    ensures acc + sumc(s, p) == sumc_iterative(s, p, acc)
{
    if |s| == 0 {
    } else {
        sumc_equivalence(s[1..], p[1..], acc + (if p[0] then s[0] else 0));
    }
}

function sumc_iterative(s: seq<int>, p: seq<bool>, acc: int) : int
    requires |s| == |p|
{
    if |s| == 0 then acc 
    else sumc_iterative(s[1..], p[1..], acc + (if p[0] then s[0] else 0))
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
        if i % 2 == 1 && v[i] % 2 == 0 {
            r := r + v[i];
        }
        i := i + 1;
    }
}
// </vc-code>

// pure-end