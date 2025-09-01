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
    ensures |s| == 0 ==> sumc(s, p) == 0
    decreases |s|
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
    decreases i
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

lemma sumc_cons(s: seq<int>, p: seq<bool>, head_s: int, head_p: bool)
    requires |s| == |p|
    ensures sumc([head_s] + s, [head_p] + p) == (if head_p then head_s else 0) + sumc(s, p)
{
}

lemma sumc_prefix_lemma(s: seq<int>, p: seq<bool>, i: nat)
    requires i <= |s|
    requires |s| == |p|
    ensures |s[..i]| == |p[..i]|
{
}

lemma square_seq_prefix_lemma(lst: seq<int>, i: nat)
    requires i <= |lst|
    ensures square_seq(lst[..i]) == square_seq(lst)[..i]
{
    assert square_seq(lst)[..i] == seq(i, j requires 0 <= j < i => lst[j] * lst[j]);
    assert square_seq(lst[..i]) == seq(i, j requires 0 <= j < i => lst[j] * lst[j]);
}

lemma add_condition_prefix_lemma(lst: seq<int>, i: nat)
    requires i <= |lst|
    ensures add_conditon(lst[..i]) == add_conditon(lst)[..i]
{
    assert add_conditon(lst)[..i] == seq(i, j requires 0 <= j < i => lst[j] >= 0 && lst[j] % 2 == 1);
    assert add_conditon(lst[..i]) == seq(i, j requires 0 <= j < i => lst[j] >= 0 && lst[j] % 2 == 1);
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
    invariant r == sumc(square_seq(lst)[..i], add_conditon(lst)[..i])
  {
    var cond := lst[i] >= 0 && lst[i] % 2 == 1;
    var sq := lst[i] * lst[i];
    
    if cond {
      r := r + sq;
    }
    
    var next_i := i + 1;
    
    assert square_seq(lst)[..next_i] == square_seq(lst)[..i] + [sq];
    assert add_conditon(lst)[..next_i] == add_conditon(lst)[..i] + [cond];
    
    assert sumc(square_seq(lst)[..next_i], add_conditon(lst)[..next_i]) == 
           sumc(square_seq(lst)[..i], add_conditon(lst)[..i]) + (if cond then sq else 0);
    
    assert r == sumc(square_seq(lst)[..i], add_conditon(lst)[..i]);
    if cond {
      assert sumc(square_seq(lst)[..next_i], add_conditon(lst)[..next_i]) == r + sq;
    } else {
      assert sumc(square_seq(lst)[..next_i], add_conditon(lst)[..next_i]) == r;
    }
    
    i := next_i;
  }
  
  assert i == |lst|;
  square_seq_prefix_lemma(lst, |lst|);
  add_condition_prefix_lemma(lst, |lst|);
  assert square_seq(lst)[..|lst|] == square_seq(lst);
  assert add_conditon(lst)[..|lst|] == add_conditon(lst);
}
// </vc-code>

