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
lemma sumc_uncons(v: seq<int>, p: seq<bool>, j: int)
  requires |v| == |p|
  requires 0 <= j < |v|
  ensures sumc(v[j..], p[j..]) == (if p[j] then v[j] else 0) + sumc(v[j+1..], p[j+1..])
{
  // Follows directly from the definition of sumc on a non-empty sequence
  assert sumc(v[j..], p[j..]) == (if p[j] then v[j] else 0) + sumc(v[j+1..], p[j+1..]);
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
  var i := |v|;
  var acc := 0;
  while i > 0
    invariant 0 <= i <= |v|
    invariant |v| == |p|
    invariant acc == sumc(v[i..], p[i..])
  {
    i := i - 1;
    if p[i] {
      acc := acc + v[i];
    } else {
      acc := acc + 0;
    }
  }
  r := acc;
}
// </vc-code>

// pure-end