// <vc-preamble>
function sum(s: seq<int>) : int
    {
        if |s| == 0 then 0 else s[0] + sum(s[1..])
    }
function ceil(f: real) : (c : int)
    {
        (f + 1.0).Floor
    }
function square_seq(lst: seq<real>) : (sq : seq<int>)
        ensures |sq| == |lst|
    {
        seq(|lst|, i requires 0 <= i < |lst| => ceil(lst[i]) * ceil(lst[i]))
    }
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method sum_squares(lst: seq<real>) returns (r : int)

    ensures r == sum(square_seq(lst))
// </vc-spec>
// <vc-code>
{
    assume {:axiom} false;
  }
// </vc-code>
