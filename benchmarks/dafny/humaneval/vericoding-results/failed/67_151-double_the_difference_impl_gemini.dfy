// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
lemma SumcAppend(s1: seq<int>, p1: seq<bool>, s2: seq<int>, p2: seq<bool>)
    requires |s1| == |p1|
    requires |s2| == |p2|
    ensures sumc(s1+s2, p1+p2) == sumc(s1, p1) + sumc(s2, p2)
    decreases |s1|
{
    if |s1| > 0 {
        SumcAppend(s1[1..], p1[1..], s2, p2);
    }
}
// </vc-helpers>

// <vc-spec>
method double_the_difference(lst: seq<int>) returns (r : int)

    ensures r == sumc(square_seq(lst), add_conditon(lst))
// </vc-spec>
// <vc-code>
{
  r := 0;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant r == sumc(square_seq(lst[..i]), add_conditon(lst[..i]))
  {
    if lst[i] >= 0 && lst[i] % 2 == 1 {
      r := r + lst[i] * lst[i];
    }
    i := i + 1;
  }
}
// </vc-code>
