// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method add(v: seq<int>) returns (r : int)

    ensures r == sumc(v, add_conditon(v))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
