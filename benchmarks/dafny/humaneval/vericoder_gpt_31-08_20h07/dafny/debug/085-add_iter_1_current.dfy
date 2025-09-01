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
lemma sumc_unfold_nonempty(s: seq<int>, p: seq<bool>)
  requires |s| == |p|
  requires |s| > 0
  ensures sumc(s, p) == (if p[0] then s[0] else 0) + sumc(s[1..], p[1..])
{
  reveal sumc();
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
  var p := add_conditon(v);
  var res := 0;
  var i := 0;
  while i < |v|
    invariant 0 <= i <= |v|
    invariant |v| == |p|
    invariant res + sumc(v[i..], p[i..]) == sumc(v, p)
  {
    calc {
      res + sumc(v[i..], p[i..]);
      == { sumc_unfold_nonempty(v[i..], p[i..]); }
      res + (if p[i] then v[i] else 0) + sumc(v[i+1..], p[i+1..]);
    }
    res := res + (if p[i] then v[i] else 0);
    i := i + 1;
  }
  r := res;
}
// </vc-code>

// pure-end