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
function sumc_iter(s: seq<int>, p: seq<bool>, i: int) : int
  requires 0 <= i <= |s|
  requires |s| == |p|
{
  if i == |s| then 0
  else (if p[i] then s[i] else 0) + sumc_iter(s, p, i + 1)
}

lemma {:induction false} SumcIterIsSumc(s: seq<int>, p: seq<bool>, i: int)
  requires 0 <= i <= |s|
  requires |s| == |p|
  ensures sumc_iter(s, p, i) == sumc(s[i..], p[i..])
{
  if i < |s| {
    calc {
      sumc_iter(s, p, i);
      (if p[i] then s[i] else 0) + sumc_iter(s, p, i + 1);
      (if p[i] then s[i] else 0) + sumc(s[i+1..], p[i+1..]); { SumcIterIsSumc(s, p, i+1); }
      sumc(s[i..], p[i..]);
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
{
  var s := square_seq(lst);
  var p := add_conditon(lst);
  var current_sum := 0;
  var i := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant |s| == |p|
    invariant current_sum == sumc_iter(s, p, 0) - sumc_iter(s, p, i)
  {
    if p[i] then
      current_sum := current_sum + s[i];
    i := i + 1;
  }
  
  SumcIterIsSumc(s, p, 0);
  SumcIterIsSumc(s, p, i); // i == |s| here

  r := current_sum;
}
// </vc-code>

