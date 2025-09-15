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

function helper_sumc(s: seq<int>, p: seq<bool>): int
  decreases |s|
  requires |s| == |p|
  ensures helper_sumc(s, p) == sumc(s, p)
{
  if |s| == 0 then
    0
  else
    (if p[0] then s[0] else 0) + helper_sumc(s[1..], p[1..])
}

function helper_add_condition(lst: seq<int>): seq<bool>
  ensures |lst| == |helper_add_condition(lst)|
  ensures helper_add_condition(lst) == add_conditon(lst)
{
  seq(|lst|, i requires 0 <= i < |lst| => i % 2 == 1 && lst[i] % 2 == 0)
}

// </vc-helpers>

// <vc-spec>
method add(v: seq<int>) returns (r : int)

    ensures r == sumc(v, add_conditon(v))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Added postcondition proofs and explicit equality */
  var p := helper_add_condition(v);
  r := helper_sumc(v, p);
  assert r == sumc(v, p) by {
    assert helper_sumc(v, p) == sumc(v, p);
  }
  assert p == add_conditon(v) by {
    assert helper_add_condition(v) == add_conditon(v);
  }
  assert r == sumc(v, add_conditon(v));
}
// </vc-code>
