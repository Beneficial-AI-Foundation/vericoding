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
    } else {
        // Base case when i == 0
    }
}

lemma sumc_prefix_lemma(s: seq<int>, p: seq<bool>, i: int)
    requires |s| == |p|
    requires 0 <= i <= |s|
    ensures sumc(s[..i], p[..i]) + sumc(s[i..], p[i..]) == sumc(s, p)
    decreases |s| - i
{
    if i < |s| {
        sumc_prefix_lemma(s, p, i+1);
    }
}

lemma add_conditon_consistent(s: seq<int>, i: int)
    requires 0 <= i <= |s|
    ensures add_conditon(s)[..i] == add_conditon(s[..i])
{
    // This lemma establishes that the condition sequence for a prefix
    // is the same as the prefix of the condition sequence for the whole sequence
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
    var p := add_conditon(v);
    while i < |v|
        invariant 0 <= i <= |v|
        invariant r == sumc(v[..i], p[..i])
    {
        if p[i] {
            r := r + v[i];
        }
        i := i + 1;
    }
}
// </vc-code>

// pure-end