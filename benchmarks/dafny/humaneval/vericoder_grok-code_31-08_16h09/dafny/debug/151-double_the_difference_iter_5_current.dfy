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
function sumc(s: seq<int>, p: seq<bool>) : int
    requires |s| == |p|
    {
        if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
    }
    lemma sumc_append(s: seq<int>, p: seq<bool>, s1: seq<int>, p1: seq<bool>)
      requires |s| == |p| && |s1| == |p1|
      ensures sumc(s + s1, p + p1) == sumc(s, p) + sumc(s1, p1)
    {
        if |s| > 0 {
            assert (s + s1)[1..] == s[1..] + s1;
            assert (p + p1)[1..] == p[1..] + p1;
            sumc_append(s[1..], p[1..], s1, p1);
        }
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

    lemma double_difference_prefix(lst: seq<int>, i: int)
      requires 0 <= i <= |lst|
      ensures sumc(square_seq(lst[..i]), add_conditon(lst[..i])) == sumc(square_seq(lst), add_conditon(lst))
      // added ensures to prove inductive step
    {
        if i == 0 {
            // base case: empty prefix
        } else {
            double_difference_prefix(lst, i - 1);
            assert add_conditon(lst) == add_conditon(lst[..(i-1)]) + add_conditon(lst[(i-1)..]);
            assert square_seq(lst) == square_seq(lst[..(i-1)]) + square_seq(lst[(i-1)..]);
            sumc_append(square_seq(lst[..(i-1)]), add_conditon(lst[..(i-1)]), square_seq(lst[(i-1)..]), add_conditon(lst[(i-1)..]));
        }
    }

    lemma double_difference_eq(lst: seq<int>)
      ensures sumc(square_seq(lst), add_conditon(lst)) == sumc(square_seq(lst), add_conditon(lst))
    {
        // trivial
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
    var sum := 0;
    var i := 0;
    while i < |lst|
        invariant 0 <= i <= |lst|
        invariant sum == sumc(square_seq(lst[..i]), add_conditon(lst[..i]))
    {
        var sq := if lst[i] >= 0 && lst[i] % 2 == 1 then lst[i] * lst[i] else 0;
        sum := sum + sq;
        i := i + 1;
    }
    r := sum;
}
// </vc-code>

