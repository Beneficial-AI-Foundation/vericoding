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
        assert sumc(s, p) == (if p[0] then s[0] else 0) + sumc(s[1..], p[1..]);
        sumc_empty(s[1..], p[1..]);
    }
}

lemma sumc_properties(s: seq<int>, p: seq<bool>, i: nat)
    requires i <= |s|
    requires |s| == |p|
    ensures sumc(s, p) == sumc(s[..i], p[..i]) + sumc(s[i..], p[i..])
{
    if i == 0 {
        assert s[..0] == [] && p[..0] == [];
        assert s[0..] == s && p[0..] == p;
        assert sumc(s[..0], p[..0]) == 0;
    } else if i < |s| {
        var s_head := s[0];
        var p_head := p[0];
        var s_tail := s[1..];
        var p_tail := p[1..];
        assert s == [s_head] + s_tail;
        assert p == [p_head] + p_tail;
        sumc_properties(s_tail, p_tail, i-1);
        assert sumc(s_tail, p_tail) == sumc(s_tail[..(i-1)], p_tail[..(i-1)]) + sumc(s_tail[(i-1)..], p_tail[(i-1)..]);
        assert s[..i] == [s_head] + s_tail[..(i-1)];
        assert p[..i] == [p_head] + p_tail[..(i-1)];
        assert sumc(s[..i], p[..i]) == (if p_head then s_head else 0) + sumc(s_tail[..(i-1)], p_tail[..(i-1)]);
        assert s[i..] == s_tail[(i-1)..];
        assert p[i..] == p_tail[(i-1)..];
        assert sumc(s, p) == (if p_head then s_head else 0) + sumc(s_tail, p_tail);
    } else {
        assert i == |s|;
        assert s[..i] == s && p[..i] == p;
        assert s[i..] == [] && p[i..] == [];
        assert sumc(s[i..], p[i..]) == 0;
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
  r := 0;
  var i := 0;
  while i < |lst|
    invariant 0 <= i <= |lst|
    invariant r == sumc(square_seq(lst[..i]), add_conditon(lst[..i]))
  {
    var sq := lst[i] * lst[i];
    var cond := lst[i] >= 0 && lst[i] % 2 == 1;
    if cond {
      r := r + sq;
    }
    
    var next_i := i + 1;
    var prefix_sq := square_seq(lst[..next_i]);
    var prefix_cond := add_conditon(lst[..next_i]);
    
    assert |prefix_sq| == next_i && |prefix_cond| == next_i;
    assert next_i > 0;  // because i < |lst|
    
    sumc_properties(prefix_sq, prefix_cond, i);
    assert sumc(prefix_sq, prefix_cond) == sumc(prefix_sq[..i], prefix_cond[..i]) + sumc(prefix_sq[i..], prefix_cond[i..]);
    
    assert prefix_sq[..i] == square_seq(lst[..i]);
    assert prefix_cond[..i] == add_conditon(lst[..i]);
    assert |prefix_sq[i..]| == 1 && |prefix_cond[i..]| == 1;
    assert prefix_sq[i..][0] == lst[i] * lst[i];
    assert prefix_cond[i..][0] == cond;
    
    assert sumc(prefix_sq[i..], prefix_cond[i..]) == (if cond then lst[i] * lst[i] else 0);
    
    assert r == sumc(square_seq(lst[..i]), add_conditon(lst[..i])) + (if cond then sq else 0);
    assert sumc(prefix_sq, prefix_cond) == r;
    
    i := next_i;
  }
  
  if |lst| == 0 {
    sumc_empty(square_seq(lst), add_conditon(lst));
  }
}
// </vc-code>

