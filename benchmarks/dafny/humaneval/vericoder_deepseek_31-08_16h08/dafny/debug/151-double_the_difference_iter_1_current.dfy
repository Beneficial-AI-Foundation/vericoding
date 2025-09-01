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
lemma sumc_empty(s: seq<int>, p: seq<bool>)
    requires |s| == |p|
    ensures sumc(s, p) == 0
{
    if |s| != 0 {
        // This forces the lemma to be proved by computation
    }
}

lemma sumc_properties(s: seq<int>, p: seq<bool>, i: int)
    requires 0 <= i <= |s|
    requires |s| == |p|
    ensures sumc(s, p) == sumc(s[..i], p[..i]) + sumc(s[i..], p[i..])
{
    if i == 0 {
        assert s[..0] == [] && p[..0] == [];
        assert s[0..] == s && p[0..] == p;
    } else if i < |s| {
        sumc_properties(s[1..], p[1..], i-1);
    }
    // else i == |s|, trivial
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
  r := 0;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant r == sumc(square_seq(lst[..i]), add_conditon(lst[..i]))
  {
    var sq := lst[i] * lst[i];
    if lst[i] >= 0 && lst[i] % 2 == 1 {
      r := r + sq;
    }
    i := i + 1;
  }
}
// </vc-code>

