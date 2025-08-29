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
function sumc_helper(s: seq<int>, p: seq<bool>, i: int) : int
    requires 0 <= i <= |s|
    requires |s| == |p|
{
    if i == 0 then 0 else (if p[i-1] then s[i-1] else 0) + sumc_helper(s, p, i-1)
}

lemma SumcEquivalence(s: seq<int>, p: seq<bool>)
    requires |s| == |p|
    ensures sumc(s, p) == sumc_helper(s, p, |s|)
{
    if |s| == 0 {
        assert sumc(s, p) == 0;
        assert sumc_helper(s, p, 0) == 0;
    } else {
        calc {
            sumc(s, p);
            == (if p[0] then s[0] else 0) + sumc(s[1..], p[1..]);
            {
                SumcEquivalence(s[1..], p[1..]);
                assert sumc(s[1..], p[1..]) == sumc_helper(s[1..], p[1..], |s|-1);
            }
            == (if p[0] then s[0] else 0) + sumc_helper(s[1..], p[1..], |s|-1);
            {
                assert sumc_helper(s, p, |s|) == (if p[0] then s[0] else 0) + sumc_helper(s[1..], p[1..], |s|-1);
            }
            == sumc_helper(s, p, |s|);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method double_the_difference(lst: seq<int>) returns (r : int)
    // post-conditions-start
    ensures r == sumc(square_seq(lst), add_conditon(lst))
    // post-conditions-end
// </vc-spec>
// <vc-code>
method double_the_difference(lst: seq<int>) returns (r : int)
    ensures r == sumc(square_seq(lst), add_conditon(lst))
{
    var sq := square_seq(lst);
    var cond := add_conditon(lst);
    var sum := 0;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant sum == sumc_helper(sq, cond, i)
    {
        if cond[i] {
            sum := sum + sq[i];
        }
        i := i + 1;
    }
    assert sum == sumc_helper(sq, cond, |lst|);
    SumcEquivalence(sq, cond);
    assert sum == sumc(sq, cond);
    r := sum;
}
// </vc-code>
