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
lemma SumcAppend(s1: seq<int>, s2: seq<int>, p1: seq<bool>, p2: seq<bool>)
    requires |s1| == |p1| && |s2| == |p2|
    ensures sumc(s1 + s2, p1 + p2) == sumc(s1, p1) + sumc(s2, p2)
    decreases |s1|
{
    if |s1| > 0 {
        SumcAppend(s1[1..], s2, p1[1..], p2);
    }
}
// </vc-helpers>

// <vc-spec>
method add(v: seq<int>) returns (r : int)

    ensures r == sumc(v, add_conditon(v))
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i := 0;
  var p := add_conditon(v);
  while i < |v|
    invariant 0 <= i <= |v|
    invariant r == sumc(v[0..i], p[0..i])
  {
    SumcAppend(v[0..i], [v[i]], p[0..i], p[i..i+1]);
    if p[i] {
      r := r + v[i];
    }
    i := i + 1;
  }
}
// </vc-code>
