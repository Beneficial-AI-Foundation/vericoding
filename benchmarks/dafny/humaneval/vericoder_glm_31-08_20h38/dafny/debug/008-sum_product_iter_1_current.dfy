function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

// <vc-helpers>
lemma {:induction} sum_prod_helper(s: seq<int>)
    ensures sum(s) * 0 <= sum(s) * prod(s)
{
    if |s| == 0 { 
        calc {
            sum(s) * 0;
            0 * 0;
            0;
            0 * 1;
            sum(s) * prod(s);
        }
    }
    else {
        calc {
            sum(s) * 0;
            0;
            sum(s[1..]) * 0 - s[0] * 0;
            sum_prod_helper(s[1..]);
            sum(s[1..]) * prod(s[1..]) - s[0] * 0;
            (s[0] + sum(s[1..])) * prod(s) - s[0] * (prod(s) - prod(s[1..]));
            { assert prod(s) == s[0] * prod(s[1..]); }
            sum(s) * prod(s) - s[0] * prod(s[1..]) + s[0] * prod(s[1..]);
            sum(s) * prod(s);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (s : int, p : int)
    // post-condition-start
    ensures s == sum(numbers)
    ensures p == prod(numbers)
    // post-condition-end
// </vc-spec>
// <vc-code>
{
    var n := |numbers|;
    s := 0;
    p := 1;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant s == sum(numbers[0..i])
        invariant p == prod(numbers[0..i])
    {
        s := s + numbers[i];
        p := p * numbers[i];
        i := i + 1;
    }
}
// </vc-code>

